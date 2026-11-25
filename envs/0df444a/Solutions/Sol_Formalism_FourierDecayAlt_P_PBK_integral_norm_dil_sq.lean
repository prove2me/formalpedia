-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.integral_norm_dil_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:21.514889+00:00
-- url     : https://prove2.me/submissions/478472f0-41ca-4bd4-832e-bb4695225118

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_comp_mul_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (f : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, ‖‖ρ‖ • f (ρ * z)‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have e : (fun z => ‖‖ρ‖ • f (ρ * z)‖ ^ 2) = fun z => ‖ρ‖ ^ 2 * ‖f (ρ * z)‖ ^ 2 := by
    funext z
    rw [norm_smul, norm_norm, mul_pow]
  rw [e, integral_const_mul, integral_comp_mul_C (fun z => ‖f z‖ ^ 2) ρ hρ, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]
end Formalism.FourierDecayAlt.P.PBK
