-- Prove2me | solution 1 for Formalism.ZF.rdp_hasDerivAt_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:21.400886+00:00
-- url     : https://prove2.me/submissions/6349aefe-140f-4e68-9366-9404d54d8a78

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole

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
theorem _root_.solution (a p w : ℂ) (hw : w ≠ p) :
    HasDerivAt (fun z => -a * (z - p)⁻¹) (a / (w - p) ^ 2) w := by
  have hwp : w - p ≠ 0 := sub_ne_zero.2 hw
  have h := (((hasDerivAt_id' w).sub_const p).inv hwp).const_mul (-a)
  convert h using 1
  all_goals first | rfl | ring | (field_simp; ring) | (simp; ring)
end Formalism.ZF
