-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_disc_center_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:13.31049+00:00
-- url     : https://prove2.me/submissions/a1333cf3-9de6-4355-bea2-a19ae9508f2b

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (t : ℝ) : ‖(21 / 20 : ℂ) + t * I‖ ≤ 21 / 20 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(21 / 20 : ℂ)‖ = 21 / 20 := by
    rw [show (21 / 20 : ℂ) = ((21 / 20 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]
end Formalism.ZeroFreeDirichlet
