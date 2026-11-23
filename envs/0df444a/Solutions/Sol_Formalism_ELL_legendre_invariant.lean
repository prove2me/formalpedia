-- Prove2me | solution 1 for Formalism.ELL.legendre_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:36.735569+00:00
-- url     : https://prove2.me/submissions/c04111ba-dccc-4872-82c2-c296b387ee42

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution : LegendreInv := by
  intro K _ l
  refine ⟨?_, ?_⟩ <;>
  simp only [legendre, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring
end Formalism.ELL
