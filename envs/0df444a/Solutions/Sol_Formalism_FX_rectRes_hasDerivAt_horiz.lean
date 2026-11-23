-- Prove2me | solution 1 for Formalism.FX.rectRes_hasDerivAt_horiz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:22.350801+00:00
-- url     : https://prove2.me/submissions/0b0e56cf-31dc-49af-a494-1e425636b1a4

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
theorem _root_.solution (c : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + c) 1 t := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const c
  simpa using h
end Formalism.FX
