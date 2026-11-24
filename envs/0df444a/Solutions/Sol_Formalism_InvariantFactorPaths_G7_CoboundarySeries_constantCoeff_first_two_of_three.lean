-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.constantCoeff_first_two_of_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:14.135514+00:00
-- url     : https://prove2.me/submissions/b331917f-3dee-4fdb-8eac-6c32aae8e514

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_has_subst_first_pair

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  rw [MvPowerSeries.constantCoeff_subst has_subst_first_pair]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    have h0 : constantCoeff ((![(X 0 : MvPowerSeries (Fin 3) K), X 1] : Fin 2 → MvPowerSeries (Fin 3) K) s) = 0 := by
      fin_cases s <;> simp
    rw [map_pow, h0, zero_pow hs]
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
