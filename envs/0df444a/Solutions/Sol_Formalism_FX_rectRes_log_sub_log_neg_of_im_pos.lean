-- Prove2me | solution 1 for Formalism.FX.rectRes_log_sub_log_neg_of_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:06.092516+00:00
-- url     : https://prove2.me/submissions/56e34fe5-248a-4c83-ad2c-d85c30eb6edd

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue

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
open Formalism Formalism.FX
namespace Formalism.FX
theorem _root_.solution {z : ℂ} (h : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
end Formalism.FX
