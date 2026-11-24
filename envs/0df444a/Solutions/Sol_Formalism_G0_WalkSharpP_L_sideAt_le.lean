-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.L_sideAt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:27.453932+00:00
-- url     : https://prove2.me/submissions/df6db927-74b9-46a7-9b3d-cf289be7edfc

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_vertexLabel_empty
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_dual
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_base_self

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
theorem _root_.solution {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}
    (L : (Fin V → Slot) → Submodule R X)
    (hdb : ∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base))
    (T : Finset (Fin V)) : L (vertexLabel T) ≤ L (fun _ => Slot.base) := by

  induction T using Finset.induction_on with
  | empty => exact le_of_eq (congrArg L vertexLabel_empty)
  | @insert v T hvT ih =>
    rw [← update_positionAt_dual]
    exact (hdb _ _).trans (by rw [update_positionAt_base_self hvT]; exact ih)
end Formalism.G0.WalkSharpP
