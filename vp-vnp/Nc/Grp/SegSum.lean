/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Blocks
import Nc.Grp.Seg

/-!
# The sum over the ways to cut a word
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {A : Type} [CommRing A]

/-- The sum over the number of letters that are taken. -/
theorem sum_segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool))
    (G : List (List Bool) → A) : ((segL sep f tk cur fs as rest out).map G).sum =
      ∑ j ∈ range (rest.length + 1), if okFlag f (tk || decide (0 < j)) then
        ((closeL sep ((rest.take j).reverse.flatten ++ cur) fs as (rest.drop j) out).map G).sum else 0 := by
  induction rest generalizing tk cur with
  | nil =>
    rw [segL_eq, takeL]
    simp only [List.append_nil, List.length_nil, zero_add, range_one, sum_singleton, lt_self_iff_false,
      decide_false, Bool.or_false, List.take_nil, List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_nil]
    split_ifs <;> simp
  | cons a r ih =>
    rw [segL_eq, takeL, List.map_append, List.sum_append, sum_range_succ']
    simp only [ih, List.length_cons, lt_self_iff_false, decide_false, Bool.or_false, List.take_zero,
      List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
      List.reverse_cons, List.flatten_append, List.flatten_cons, List.append_nil, List.append_assoc, Bool.true_or,
      Nat.zero_lt_succ, decide_true, Bool.or_true]
    rw [add_comm]
    congr 1
    split_ifs <;> simp

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

theorem cat_snoc {m : ℕ} (X : Fin m → List Γ) (y : List Γ) :
    cat (Fin.snoc X y : Fin (m + 1) → List Γ) = cat X ++ y := by
  simp only [cat, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Cutting off the last segment. -/
theorem sum_cut {m : ℕ} (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (p : Fin (m + 1) → List Γ → Prop)
    [∀ b, DecidablePred (p b)] (H : (Fin (m + 1) → List Γ) → A) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter (fun X => cat X = l ∧ ∀ b, p b (X b)), H X =
      ∑ j ∈ range (l.length + 1), if p (Fin.last m) (l.drop (l.length - j)) then
        ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
          (fun X => cat X = l.take (l.length - j) ∧ ∀ b, p b.castSucc (X b)),
          H (Fin.snoc X (l.drop (l.length - j))) else 0 := by
  have hinit : ∀ X : Fin (m + 1) → List Γ, cat X = cat (Fin.init X) ++ X (Fin.last m) := by
    intro X
    simpa only [Fin.snoc_init_self] using cat_snoc (Fin.init X) (X (Fin.last m))
  have hdrop : ∀ X : Fin (m + 1) → List Γ, cat X = l →
      cat (Fin.init X) = l.take (l.length - (X (Fin.last m)).length) ∧
      X (Fin.last m) = l.drop (l.length - (X (Fin.last m)).length) := by
    intro X hX
    subst l
    rw [hinit, List.length_append, Nat.add_sub_cancel]
    simp
  rw [← sum_fiberwise_of_maps_to (s := (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
    (fun X => cat X = l ∧ ∀ b, p b (X b))) (t := range (l.length + 1)) (g := fun X => (X (Fin.last m)).length)]
  · refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have hlast (X : Fin (m + 1) → List Γ) (hl : cat X = l) (hj : (X (Fin.last m)).length = j) :
        X (Fin.last m) = l.drop (l.length - j) := hj ▸ (hdrop X hl).2
    split_ifs with hp
    · refine sum_nbij' (i := fun X => Fin.init X)
        (j := fun X => Fin.snoc X (l.drop (l.length - j)))
        ?_ ?_ ?_ (fun X _ => Fin.init_snoc _ _) ?_
      · intro X hX
        simp only [mem_filter, Fintype.mem_piFinset] at hX ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hX
        exact ⟨fun b => h1 _, h4 ▸ (hdrop X h2).1, fun b => h3 _⟩
      · intro X hX
        obtain ⟨h1, h2, h3⟩ := mem_filter.1 hX
        have hlen : (l.drop (l.length - j)).length = j := by rw [List.length_drop]; omega
        simp only [mem_filter, Fintype.mem_piFinset, Fin.forall_fin_succ', Fin.snoc_castSucc,
          Fin.snoc_last, cat_snoc, h2, List.take_append_drop, hp, hlen, and_true, true_and]
        exact ⟨⟨Fintype.mem_piFinset.1 h1, mem_wordsLe.2 (by omega)⟩, h3⟩
      all_goals
        intro X hX
        obtain ⟨⟨-, hl, -⟩, hj⟩ := (by simpa only [mem_filter] using hX)
        rw [← hlast X hl hj, Fin.snoc_init_self]
    · refine sum_eq_zero fun X hX => ?_
      simp only [mem_filter] at hX
      obtain ⟨⟨-, h2, h3⟩, h4⟩ := hX
      exfalso
      apply hp
      rw [← hlast X h2 h4]
      exact h3 _
  · intro X hX
    simp only [mem_filter] at hX
    rw [mem_range, ← hX.2.1, hinit, List.length_append]
    omega

theorem drop_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    (l.map bits).reverse.drop j = ((l.take (l.length - j)).map bits).reverse := by
  rw [List.drop_reverse, List.length_map, List.map_take]

theorem take_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    ((l.map bits).reverse.take j).reverse.flatten = (l.drop (l.length - j)).flatMap bits := by
  rw [List.take_reverse, List.length_map, List.reverse_reverse, ← List.map_drop, List.flatMap_def]

theorem ofFn_rev {α : Type} {m : ℕ} (f : Fin (m + 1) → α) :
    (List.ofFn f).reverse = f (Fin.last m) :: (List.ofFn fun b => f b.castSucc).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem sum_segL_start (sep : List Bool) (bits : Γ → List Bool) (T : ℕ) {m : ℕ} (fl : Fin (m + 1) → ℕ)
    (acc : Fin (m + 1) → List Bool) (l : List Γ) (hT : l.length ≤ T) (out : List (List Bool))
    (G : List (List Bool) → A) :
    ((segL sep (fl (Fin.last m)) false (sep ++ acc (Fin.last m)) (List.ofFn fun b => fl b.castSucc).reverse
      (List.ofFn fun b => acc b.castSucc).reverse (l.map bits).reverse out).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G ((List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) ++ out) := by
  rw [sum_segL, sum_cut T l hT (fun b x => okFlag (fl b) (decide (x ≠ [])) = true),
    List.length_reverse, List.length_map]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
    apply decide_eq_decide.2
    rw [← List.length_pos_iff, List.length_drop]
    omega
  simp only [Bool.false_or, e1]
  refine if_congr Iff.rfl ?_ rfl
  rw [take_rev, drop_rev]
  cases m with
  | zero =>
    have e : ∀ X : Fin 0 → List Γ, cat X = [] := fun X => by simp [cat]
    have last (X : Fin 0 → List Γ) (y : List Γ) : (Fin.snoc X y : Fin 1 → List Γ) 0 = y :=
      Fin.snoc_last (α := fun _ => List Γ) y X
    by_cases h : l.take (l.length - j) = []
    · simp [closeL, e, h, List.ofFn_succ, last]
    · have hne : ¬ (l.length - j = 0 ∨ l = []) := by simpa using h
      simp [closeL, e, Ne.symm h, hne]
  | succ m =>
    rw [ofFn_rev, ofFn_rev, closeL]
    have h := sum_segL_start sep bits T (fun b => fl b.castSucc) (fun b => acc b.castSucc)
      (l.take (l.length - j)) ((List.length_take_le' _ _).trans hT)
      (((l.drop (l.length - j)).flatMap bits ++ (sep ++ acc (Fin.last (m + 1)))) :: out) G
    simp only [List.headD_cons, List.tail_cons]
    rw [h]
    refine sum_congr rfl fun X _ => ?_
    rw [List.ofFn_succ' (n := m + 1)]
    simp
termination_by m

/-- **The sum over the ways to cut a word.** -/
theorem sum_segRow' (sep : List Bool) {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (bits : Γ → List Bool) (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (G : List (List Bool) → A) :
    ((segRow sep (List.ofFn fl).reverse (List.ofFn acc).reverse (l.map bits).reverse).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G (List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := sum_segL_start sep bits T fl acc l hT [] G
  rw [ofFn_rev, ofFn_rev, segRow]
  simpa only [List.headD_cons, List.tail_cons, List.append_nil] using h

end Nc.Grp
