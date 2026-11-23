-- Prove2me | solution 1 for Formalism.DivisorInequality.places_ell_weighted_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:36.963929+00:00
-- url     : https://prove2.me/submissions/df9cafab-730c-4972-8636-e8d8b3a58641

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Theorems.Thm_Formalism_DivisorInequality_ramified_places_weighted_sum_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DivisorInequality
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ y ∈ S, lw y * (2 / ellw y ^ 2) ≤ 1 := by
  have h := ramified_places_weighted_sum_le_one K (S.filter fun y => (0:ℝ) ≤ (ramw y : ℝ))
  rw [Finset.sum_filter] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)) h
  by_cases hr : (0:ℝ) ≤ (ramw y : ℝ)
  · rw [if_pos hr, ellw, div_pow, Real.sq_sqrt hr, div_div_eq_mul_div]
    ring
  · rw [if_neg hr, ellw, Real.sqrt_eq_zero'.mpr (not_le.mp hr).le]
    simp
end Formalism.DivisorInequality
