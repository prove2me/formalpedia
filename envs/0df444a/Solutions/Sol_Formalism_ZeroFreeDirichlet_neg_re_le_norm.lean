-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.neg_re_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:21.703805+00:00
-- url     : https://prove2.me/submissions/4992414d-c279-4a30-ac69-8a343566cf8f

import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaLogDerivLandauBound

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
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  linarith [neg_le_abs x.re, Complex.abs_re_le_norm x]
end Formalism.ZeroFreeDirichlet
