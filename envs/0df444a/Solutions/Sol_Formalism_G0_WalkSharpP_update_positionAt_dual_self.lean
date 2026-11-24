-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.update_positionAt_dual_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:07.232469+00:00
-- url     : https://prove2.me/submissions/3918f8b3-a652-4aeb-b8cf-044e3395cfa8

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} {v : Fin V} (hv : v ∈ B) :
    Function.update (vertexLabel B) v Slot.dual = vertexLabel B := by
  rw [update_positionAt_dual, Finset.insert_eq_of_mem hv]
end Formalism.G0.WalkSharpP
