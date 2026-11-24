-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.top_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:05.829883+00:00
-- url     : https://prove2.me/submissions/1dbb5553-f7da-47f8-b5dd-c9c62145c8f9

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_le_top

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
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} {v w : Fin V} (hw : (w : ℕ) = top B + 1) :
    top (insert w (B.erase v)) = top B + 1 := by

  apply le_antisymm
  · apply Finset.sup_le
    intro u hu
    show (u : ℕ) ≤ top B + 1
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, hw]
    · have := le_top (Finset.mem_of_mem_erase h)
      omega
  · rw [← hw]
    exact le_top (Finset.mem_insert_self w _)
end Formalism.G0.WalkSharpP
