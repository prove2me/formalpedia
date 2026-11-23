-- Prove2me | solution 1 for Formalism.FX.rectRes_log_sub_log_neg_of_im_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:22.294491+00:00
-- url     : https://prove2.me/submissions/4938f661-1d46-45b9-b451-f836e0456520

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
theorem _root_.solution {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by
  have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
end Formalism.FX
