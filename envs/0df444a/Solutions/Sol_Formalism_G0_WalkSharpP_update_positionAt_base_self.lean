-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.update_positionAt_base_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:00.08981+00:00
-- url     : https://prove2.me/submissions/5a59791e-93ba-4b2a-854c-b7073a73910b

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
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} {v : Fin V} (hv : v ∉ B) :
    Function.update (vertexLabel B) v Slot.base = vertexLabel B := by
  funext u
  by_cases h : u = v
  · subst h
    simp [vertexLabel, hv]
  · simp [Function.update_apply, h]
end Formalism.G0.WalkSharpP
