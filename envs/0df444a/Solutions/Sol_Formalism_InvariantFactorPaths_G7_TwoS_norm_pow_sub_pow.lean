-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.norm_pow_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:07.960426+00:00
-- url     : https://prove2.me/submissions/54dfbe0d-0395-4eff-8ede-424d659a0381

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
import Theorems.Thm_P2M_Bl_general_b_fact_right____goal1_c913391e7c08


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
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {p : ℕ} {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (h : ‖a - b‖ ≤ (p : ℝ)⁻¹) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ (p : ℝ)⁻¹ := by
  first | exact Bl.general_b_fact_right'''.goal1 .. | (apply Bl.general_b_fact_right'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right'''.goal1 <;> assumption) | (apply @Bl.general_b_fact_right'''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right'''.goal1 <;> assumption) | (apply @Bl.general_b_fact_right'''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb h k | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb h | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha hb | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b ha | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a b | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p a | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› p | exact @Bl.general_b_fact_right'''.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_right'''.goal1 K ‹_› | exact @Bl.general_b_fact_right'''.goal1 K
end Formalism.InvariantFactorPaths.G7.TwoS
