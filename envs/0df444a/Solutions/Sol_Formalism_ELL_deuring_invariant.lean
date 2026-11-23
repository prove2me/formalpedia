-- Prove2me | solution 1 for Formalism.ELL.deuring_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:08.662676+00:00
-- url     : https://prove2.me/submissions/97d9237e-90b5-48f0-ba54-f44f92237e93

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
theorem _root_.solution : DeuringInv := by
  intro K _ a
  refine ⟨?_, ?_⟩ <;>
  simp only [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄] <;> ring
end Formalism.ELL
