-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.enter_positionAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:28.325272+00:00
-- url     : https://prove2.me/submissions/712af6a2-e6d9-443b-bb9b-1f081c3bb4b9

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
    (L : (Fin V → Slot) → Submodule R X) (π : R) (b : Fin V → ℕ)
    (henter : ∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual))
    (T : Finset (Fin V)) :
    ∀ x ∈ L (fun _ => Slot.base), π ^ (∑ u ∈ T, b u) • x ∈ L (vertexLabel T) := by

  induction T using Finset.induction_on with
  | empty => intro x hx; simpa [vertexLabel_empty] using hx
  | @insert v T hvT ih =>
    intro x hx
    rw [Finset.sum_insert hvT, pow_add, mul_smul, ← update_positionAt_dual]
    apply henter
    rw [update_positionAt_base_self hvT]
    exact ih x hx
end Formalism.G0.WalkSharpP
