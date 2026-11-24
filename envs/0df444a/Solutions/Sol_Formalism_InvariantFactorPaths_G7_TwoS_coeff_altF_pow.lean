-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.coeff_altF_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:37.429159+00:00
-- url     : https://prove2.me/submissions/7984acc9-8d9f-465b-ad81-0136e77763b8

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
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj


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
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ l) (altF K p) = (-1) ^ l := by
  rw [altF, PowerSeries.coeff_mk, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (powq_inj hp h).symm
  · intro h
    exact absurd (mem_range.2 (lt_powq hp l)) h
end Formalism.InvariantFactorPaths.G7.TwoS
