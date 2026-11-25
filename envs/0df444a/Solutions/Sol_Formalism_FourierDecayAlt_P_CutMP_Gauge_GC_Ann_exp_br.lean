-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.exp_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:33.53291+00:00
-- url     : https://prove2.me/submissions/86113bc8-593c-45eb-bd0a-05a0af7f010a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
