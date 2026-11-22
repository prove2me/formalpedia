-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_perron_integrand_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:29.01754+00:00
-- url     : https://prove2.me/submissions/f88a3e63-92a9-4233-99de-72445cf7f057

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound

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
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fchi χ y w‖ = ‖negLD χ w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  unfold Fchi
  rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
end Formalism.ZeroFreeDirichlet
