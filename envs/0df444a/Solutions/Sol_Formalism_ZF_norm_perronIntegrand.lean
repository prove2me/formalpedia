-- Prove2me | solution 1 for Formalism.ZF.norm_perronIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:08.406212+00:00
-- url     : https://prove2.me/submissions/47b8230c-36c7-40c0-861d-9dc931b0b2a7

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle

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
theorem _root_.solution (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fy y w‖ = ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  simp only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]
end Formalism.ZF
