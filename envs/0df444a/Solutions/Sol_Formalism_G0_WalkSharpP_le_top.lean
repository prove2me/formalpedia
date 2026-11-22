-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.le_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:26.735452+00:00
-- url     : https://prove2.me/submissions/e6ffc20b-8d5d-4e28-ae0f-e393d7a8b1f2

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
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} {u : Fin V} (h : u ∈ B) : (u : ℕ) ≤ top B := Finset.le_sup (f := fun u : Fin V => (u : ℕ)) h
end Formalism.G0.WalkSharpP
