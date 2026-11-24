-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.update_positionAt_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:47.70546+00:00
-- url     : https://prove2.me/submissions/10dac5fa-91d9-4ea3-ad8e-f6f0fc02fd6f

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

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
theorem _root_.solution {V : ℕ} (B : Finset (Fin V)) (v : Fin V) :
    Function.update (vertexLabel B) v Slot.base = vertexLabel (B.erase v) := by

  funext u
  by_cases h : u = v
  · subst h
    simp [vertexLabel]
  · simp [vertexLabel, Function.update_apply, h]
end Formalism.G0.WalkSharpP
