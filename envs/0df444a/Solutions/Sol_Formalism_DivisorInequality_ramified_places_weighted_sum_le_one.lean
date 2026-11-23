-- Prove2me | solution 1 for Formalism.DivisorInequality.ramified_places_weighted_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:34.035566+00:00
-- url     : https://prove2.me/submissions/3f7c46d6-8366-4623-8ede-11939a6dfc54

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
import Theorems.Thm_Formalism_DivisionValues_prime_mod_six_of_large
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_place_sum
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ramified_basic_bound


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
    ∑ y ∈ S, lw y * ((ramw y : ℝ) * (2 / (plc y : ℝ) ^ 2)) ≤ 1 := by
  have h1 := Formalism.EigenvalueLevelCeiling.place_sum K S (fun p => 2 / (p : ℝ) ^ 2) (fun p => by positivity)
  have h2 := Formalism.DivisionValues.prime_mod_six_of_large.1 (S.image plc) (by
    intro p hp
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hp
    exact (Formalism.EigenvalueLevelCeiling.ramified_basic_bound K y).1)
  have h3 : ∑ p ∈ S.image plc, Real.log (p : ℝ) * (2 / (p : ℝ) ^ 2) =
      ∑ p ∈ S.image plc, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_congr rfl (fun p _ => by ring)
  linarith
end Formalism.DivisorInequality
