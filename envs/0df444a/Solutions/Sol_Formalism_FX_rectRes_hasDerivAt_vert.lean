-- Prove2me | solution 1 for Formalism.FX.rectRes_hasDerivAt_vert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:05.824506+00:00
-- url     : https://prove2.me/submissions/72fa575a-dad3-44a9-830b-4a94862bd8c5

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
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c
  simpa using h
end Formalism.FX
