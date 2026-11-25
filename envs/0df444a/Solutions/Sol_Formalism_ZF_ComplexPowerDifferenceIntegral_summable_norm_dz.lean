-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:32.649857+00:00
-- url     : https://prove2.me/submissions/8ca9a9f4-ac6f-4478-87e7-65d193b8bac8

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_dz_le
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_shift

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
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dz_le hs n)
    ((summable_shift (by linarith : -s.re - 1 < -1)).mul_left _)
end Formalism.ZF.ComplexPowerDifferenceIntegral
