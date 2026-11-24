-- Prove2me | solution 1 for Formalism.ZF.rdp_rectInt_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:38.904021+00:00
-- url     : https://prove2.me/submissions/1b6fafe0-c7df-487e-b8da-00eaa5979b80

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Theorems.Thm_Formalism_ZF_rdp_horiz
import Theorems.Thm_Formalism_ZF_rdp_vert

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
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (a p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 := by
  simp only [rectInt]
  rw [rdp_horiz a p y0 x0 x1 (ne_of_lt h3), rdp_horiz a p y1 x0 x1 (ne_of_gt h4),
    rdp_vert a p x1 y0 y1 (ne_of_gt h2), rdp_vert a p x0 y0 y1 (ne_of_lt h1)]
  ring
end Formalism.ZF
