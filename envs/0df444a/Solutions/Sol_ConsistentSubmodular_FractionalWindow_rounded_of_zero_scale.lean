-- Prove2me | solution 1 for ConsistentSubmodular.FractionalWindow.rounded_of_zero_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:45.735463+00:00
-- url     : https://prove2.me/submissions/46a20b09-c172-4984-9b62-6c51f07d77e0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_deletion_first

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

theorem value_le_bufferedOptimum (N Q : Finset (Fin n)) (k : ℕ) :
    f.value Q ≤ f.bufferedOptimum N Q k := by
  simpa using f.le_bufferedOptimum (N := N) (Q := Q) (k := k)
    (Finset.empty_subset N) (Nat.zero_le k)

/-- Zero old scale needs neither normalization nor nonempty old cores. -/
theorem bufferedOptimum_eq_of_zero_scale {N : Finset (Fin n)} {k : ℕ}
    (hzero : f.bufferedOptimum N ∅ k = 0) (Q : Finset (Fin n)) :
    f.bufferedOptimum N Q k = f.value Q := by
  have hu := f.bufferedOptimum_le N Q k
  have hl := f.value_le_bufferedOptimum N Q k
  have h0 := f.nonnegative ∅
  rw [hzero] at hu
  linarith

end Objective

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem solution (hV : f.bufferedOptimum old ∅ κ = 0)
    (H L : ℕ) (hL : 2 ≤ L) : Nonempty (RoundedWindow W H L) := by
  classical
  obtain ⟨entry, helen, he0, he1, henodes⟩ :=
    SetOperationPath.exists_deletion_first initial (∅ : Finset (Fin n))
  obtain ⟨exit, hxlen, hx0, hx1, hxnodes⟩ :=
    SetOperationPath.exists_deletion_first (∅ : Finset (Fin n)) terminal
  have hinitcard : initial.card ≤ κ := by simpa only [W.core_initial] using W.core_card 0
  have htermcard : terminal.card ≤ κ := by
    simpa only [W.core_terminal] using W.core_card (Fin.last (3 * N + 1))
  have hinitold : initial ⊆ old := by simpa only [W.core_initial] using W.core_subset 0
  have htermold : terminal ⊆ old := by
    simpa only [W.core_terminal] using W.core_subset (Fin.last (3 * N + 1))
  have hcard (A : Finset (Fin n)) (hA : A.card ≤ κ) :
      (A.card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H := by
    have ha : (A.card : ℝ) ≤ κ := by exact_mod_cast hA
    have hd : 0 ≤ (κ : ℝ) / N := by positivity
    have hh : (0 : ℝ) ≤ H := by positivity
    linarith
  have hcoef : α - 2 / N ≤ 1 := by
    have hd : 0 ≤ (2 : ℝ) / N := by positivity
    linarith [W.level_le]
  have hgood (t : ℕ) (A : Finset (Fin n)) :
      (α - 2 / N) * f.bufferedOptimum old (Q t) κ ≤ f.value (Q t ∪ A) := by
    rw [f.bufferedOptimum_eq_of_zero_scale hV]
    exact (mul_le_of_le_one_left (f.nonnegative _) hcoef).trans
      (f.monotone _ _ Finset.subset_union_left)
  refine ⟨{
    entry := entry
    exit := exit
    entry_initial := he0
    join := he1.trans hx0.symm
    exit_terminal := hx1
    length := ?_
    entry_subset := ?_
    exit_subset := ?_
    entry_card := ?_
    exit_card := ?_
    entry_good := fun j => hgood 0 _
    exit_good := fun j => hgood T _
    checkpoint_tests := ?_ }⟩
  · rw [helen, hxlen]
    simp only [recourse, Finset.sdiff_empty, Finset.empty_sdiff,
      Finset.union_empty, Finset.empty_union]
    have hh := Nat.mul_le_mul_right κ hL
    omega
  · intro j
    have hh : entry.node j ⊆ initial := by simpa only [Finset.union_empty] using (henodes j).2.1
    exact hh.trans hinitold
  · intro j
    have hh : exit.node j ⊆ terminal := by simpa only [Finset.empty_union] using (hxnodes j).2.1
    exact hh.trans htermold
  · intro j
    apply hcard
    have hh := (henodes j).2.2
    simpa only [Finset.card_empty, Nat.zero_le, max_eq_left] using hh.trans
      (by simpa only [Finset.card_empty, Nat.zero_le, max_eq_left] using hinitcard)
  · intro j
    apply hcard
    have hh := (hxnodes j).2.2
    simpa only [Finset.card_empty, Nat.zero_le, max_eq_right] using hh.trans
      (by simpa only [Finset.card_empty, Nat.zero_le, max_eq_right] using htermcard)
  · intro i
    rw [hV, zero_div, sub_zero, he1, Finset.union_empty,
      f.bufferedOptimum_eq_of_zero_scale hV]
    exact mul_le_of_le_one_left (f.nonnegative _) (by linarith [W.level_le])

end
