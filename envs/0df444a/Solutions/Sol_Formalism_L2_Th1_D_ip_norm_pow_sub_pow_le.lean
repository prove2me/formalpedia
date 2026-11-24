-- Prove2me | solution 1 for Formalism.L2.Th1.D.ip_norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:16.505139+00:00
-- url     : https://prove2.me/submissions/7d444f36-b4b4-4afa-b48b-4d8def91c620

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Bl_ProductIntegralBounds_goal1
import Theorems.Thm_Bl_general_b_fact_upper_goal1
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
namespace Formalism.L2.Th1.D
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  first | exact Bl.general_b_fact_upper.goal1 .. | (apply Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy n | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx hy | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y hx | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x y | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› x | exact @Bl.general_b_fact_upper.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_upper.goal1 K ‹_› | exact @Bl.general_b_fact_upper.goal1 K
end Formalism.L2.Th1.D
