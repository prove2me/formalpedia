-- Prove2me | solution 1 for Formalism.ZF.integral_eq_intervalIntegral_add_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:15.0567+00:00
-- url     : https://prove2.me/submissions/0ac226de-c66d-4fd3-ab49-2d911a6a0cbd

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]
end Formalism.ZF
