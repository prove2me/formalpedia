-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.mem_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:47.620998+00:00
-- url     : https://prove2.me/submissions/d7ce08e0-3a3d-4d38-84c8-27534ad0bbdc

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
theorem _root_.solution {V : ℕ} {m : ℕ} {B : Finset (Fin V)} {i : Fin V → ℕ} :
    i ∈ idx m B ↔ ∀ u, (u ∈ B → i u < m) ∧ (u ∉ B → i u = 0) := by

  simp only [idx, Fintype.mem_piFinset]
  refine forall_congr' fun u => ?_
  by_cases h : u ∈ B <;> simp [h]
end Formalism.G0.WalkSharpP
