-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.constantCoeff_Gser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.811812+00:00
-- url     : https://prove2.me/submissions/ce9b8da3-c952-4727-ba8c-45dcad613ffd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Aser_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_constantCoeff_AA
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_Aser__eq_f9daf344d726


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS
open Formalism.InvariantFactorPaths.G7.TwoS
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {K : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (c c' : K) :
    MvPowerSeries.constantCoeff (Gser p c c') = 0 := by
  simp [Gser, Aser_eq, Aser'_eq, constantCoeff_AA K hp]
end Formalism.InvariantFactorPaths.G7.TwoS
