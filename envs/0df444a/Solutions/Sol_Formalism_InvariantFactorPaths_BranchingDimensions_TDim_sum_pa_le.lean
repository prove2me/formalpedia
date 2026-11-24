-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_pa_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:11.801707+00:00
-- url     : https://prove2.me/submissions/7a42c91b-e808-4dcb-a1b0-a62aed072a42

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_ite_const_le

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution {Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (hL0 : 0 ≤ L)
    (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns)
    (hG : ∀ i j, i < j → j < n → G la i j ≤ L) :
    ∑ j ∈ range n, ∑ i ∈ range j, pa la i j ≤ 4 * (Ns : ℝ) ^ 2 * L := by
  have hnz : ((range n).filter fun m => la m ≠ 0).card ≤ 2 * Ns := by
    have hsub : ((range n).filter fun m => la m ≠ 0) ⊆
        ((range n).filter fun m => 0 < la m) ∪ ((range n).filter fun m => la m < 0) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases lt_or_gt_of_ne hm.2 with h | h
      · exact Or.inr ⟨hm.1, h⟩
      · exact Or.inl ⟨hm.1, h⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((range n).filter fun m => 0 < la m)
      ((range n).filter fun m => la m < 0)
    omega
  have hrow : ∀ j ∈ range n, ∑ i ∈ range j, pa la i j ≤
      (if la j ≠ 0 then (2 * (Ns : ℝ)) * L else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hj0 : la j = 0
    · rw [if_neg (show ¬(la j ≠ 0) from fun h => h hj0)]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      unfold pa
      rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.2 hj0)]
    · rw [if_pos hj0]
      have h1 : ∑ i ∈ range j, pa la i j ≤ ∑ i ∈ range j, (if la i ≠ 0 then L else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        unfold pa
        by_cases hi0 : la i = 0
        · rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0),
            if_neg (show ¬(la i ≠ 0) from fun h => h hi0)]
          all_goals exact le_rfl
        · rw [if_pos ⟨hi0, hj0⟩, if_pos hi0]
          exact hG i j hi hj
      have h2 : ∑ i ∈ range j, (if la i ≠ 0 then L else 0) ≤
          ∑ i ∈ range n, (if la i ≠ 0 then L else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hx) hj))
        intro i _ _
        split_ifs
        · exact hL0
        · exact le_rfl
      have h3 : ∑ i ∈ range n, (if la i ≠ 0 then L else 0) ≤ ((2 * Ns : ℕ) : ℝ) * L :=
        sum_ite_const_le (fun m => la m ≠ 0) hnz hL0
      have h4 : ((2 * Ns : ℕ) : ℝ) = 2 * (Ns : ℝ) := by push_cast; ring
      rw [h4] at h3
      linarith
  calc ∑ j ∈ range n, ∑ i ∈ range j, pa la i j
      ≤ ∑ j ∈ range n, (if la j ≠ 0 then (2 * (Ns : ℝ)) * L else 0) := Finset.sum_le_sum hrow
    _ ≤ ((2 * Ns : ℕ) : ℝ) * ((2 * (Ns : ℝ)) * L) :=
        sum_ite_const_le (fun m => la m ≠ 0) hnz (mul_nonneg (by positivity) hL0)
    _ = 4 * (Ns : ℝ) ^ 2 * L := by push_cast; ring
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
