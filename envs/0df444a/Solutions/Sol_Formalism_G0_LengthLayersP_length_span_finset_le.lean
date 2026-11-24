-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_span_finset_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:23.620143+00:00
-- url     : https://prove2.me/submissions/b6bb34b5-36a5-4a13-bced-95b9d900db2f

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_length_sup_le
import Theorems.Thm_Formalism_G0_LengthLayersP_length_span_singleton_le

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
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0) :
    Module.length O ↥(Submodule.span O (D : Set X)) ≤ ((D.card * s : ℕ) : ℕ∞) := by
  classical
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    rw [Finset.coe_empty, Submodule.span_empty, Module.length_eq_zero]
    simp
  · intro x D hxD ih hD
    rw [Finset.coe_insert, Submodule.span_insert]
    calc Module.length O ↥(O ∙ x ⊔ Submodule.span O (D : Set X))
        ≤ Module.length O ↥(O ∙ x) + Module.length O ↥(Submodule.span O (D : Set X)) :=
          length_sup_le _ _
      _ ≤ (s : ℕ∞) + ((D.card * s : ℕ) : ℕ∞) :=
          add_le_add (length_span_singleton_le π hπ s x (hD x (Finset.mem_insert_self x D)))
            (ih (fun y hy => hD y (Finset.mem_insert_of_mem hy)))
      _ = (((insert x D).card * s : ℕ) : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hxD]; push_cast; ring
end Formalism.G0.LengthLayersP
