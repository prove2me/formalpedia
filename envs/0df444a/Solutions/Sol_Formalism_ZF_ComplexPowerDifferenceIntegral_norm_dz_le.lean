-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.norm_dz_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:03.714394+00:00
-- url     : https://prove2.me/submissions/b85b18fe-108b-4b8c-97f0-7948f7519996

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_d_eq
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_eint_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dz, d_eq ha s, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eint_le ha hs) (norm_nonneg _)
end Formalism.ZF.ComplexPowerDifferenceIntegral
