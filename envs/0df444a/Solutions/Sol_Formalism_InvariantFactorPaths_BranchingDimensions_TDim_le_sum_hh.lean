-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.le_sum_hh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:17.659055+00:00
-- url     : https://prove2.me/submissions/1f01db59-8b1b-4dee-aecf-d2624aae02a0

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_fT_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_nonneg
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_le

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
theorem _root_.solution {z L : ℝ} (hz : 0 ≤ z) (hL : Real.log (1 + z) ≤ L) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (k' : ℕ) :
    fT k' z - ((Icc 1 k' \ D).card : ℝ) * L ≤ ∑ d ∈ D, hh z d := by
  have hset : Icc 1 k' \ (Icc 1 k' ∩ D) = Icc 1 k' \ D := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit : ∑ d ∈ Icc 1 k' \ (Icc 1 k' ∩ D), hh z d + ∑ d ∈ Icc 1 k' ∩ D, hh z d =
      ∑ d ∈ Icc 1 k', hh z d :=
    Finset.sum_sdiff (fun x hx => (Finset.mem_inter.mp hx).1)
  rw [hset] at hsplit
  have h1 : ∑ d ∈ Icc 1 k' ∩ D, hh z d ≤ ∑ d ∈ D, hh z d :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_inter.mp hx).2)
      (fun x hx _ => hh_nonneg hz (hD x hx))
  have h2 : ∑ d ∈ Icc 1 k' \ D, hh z d ≤ ∑ d ∈ Icc 1 k' \ D, L :=
    Finset.sum_le_sum fun x hx =>
      (hh_le hz (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hx).1).1).trans hL
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  rw [fT_eq]
  linarith
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
