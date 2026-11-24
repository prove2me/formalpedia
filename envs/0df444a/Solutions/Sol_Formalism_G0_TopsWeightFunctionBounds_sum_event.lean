-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.sum_event
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:47.9451+00:00
-- url     : https://prove2.me/submissions/f6a08a49-9053-42fb-be47-40ceeab7a940

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_sum_list
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Lst_nodup
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Lst_toFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n i : ℕ} (hi : i < n) (s : St) :
    ∑ T ∈ (Finset.range n).powerset,
      (if i ∈ T ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ T))) = .bad then
        ∏ p ∈ Finset.range n, wP δ T p else 0) = δ * Wt R L₂ δ (n - 1) s := by
  have hS := Lst_toFinset hi
  have hr : Finset.range n = insert i ((Finset.range n).erase i) :=
    (Finset.insert_erase (Finset.mem_range.2 hi)).symm
  have hiS : i ∉ (Finset.range n).erase i := Finset.notMem_erase i _
  rw [hr, Finset.sum_powerset_insert hiS]
  have z1 : ∑ U ∈ ((Finset.range n).erase i).powerset,
      (if i ∈ U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ insert i ((Finset.range n).erase i), wP δ U p else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    have : i ∉ U := fun h => hiS (Finset.mem_powerset.1 hU h)
    simp [this]
  rw [z1, zero_add]
  have e2 : ∀ U ∈ ((Finset.range n).erase i).powerset,
      (if i ∈ insert i U ∧ runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ insert i U))) = .bad then
        ∏ p ∈ insert i ((Finset.range n).erase i), wP δ (insert i U) p else 0) =
      δ * (if runS R L₂ s ((Lst n i).map (fun p => decide (p ∈ U))) = .bad then
        ∏ p ∈ (Lst n i).toFinset, wP δ U p else 0) := by
    intro U _
    have hmap : (Lst n i).map (fun q => decide (q ∈ insert i U)) =
        (Lst n i).map (fun q => decide (q ∈ U)) := by
      apply List.map_congr_left
      intro q hq
      have hq' : q ∈ (Finset.range n).erase i := by rw [← hS, List.mem_toFinset]; exact hq
      have : q ≠ i := Finset.ne_of_mem_erase hq'
      simp [Finset.mem_insert, this]
    have hprod : ∏ q ∈ (Finset.range n).erase i, wP δ (insert i U) q =
        ∏ q ∈ (Lst n i).toFinset, wP δ U q := by
      rw [hS]
      apply Finset.prod_congr rfl
      intro q hq
      have : q ≠ i := Finset.ne_of_mem_erase hq
      simp [wP, Finset.mem_insert, this]
    have hw : wP δ (insert i U) i = δ := by simp [wP]
    rw [Finset.prod_insert hiS, hw, hmap, hprod]
    simp only [Finset.mem_insert_self, true_and]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, ← hS, sum_list _ (Lst_nodup n i)]
  simp [Lst]
end Formalism.G0.TopsWeightFunctionBounds
