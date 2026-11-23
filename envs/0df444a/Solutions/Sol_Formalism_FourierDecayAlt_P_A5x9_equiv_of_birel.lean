-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.equiv_of_birel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:14.643885+00:00
-- url     : https://prove2.me/submissions/24608c31-1071-4177-a680-b37fedeb0422

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {α β : Type} (A : α → Prop) (B : β → Prop) (C : β → α → Prop)
    (c1 : ∀ a, A a → ∃ b, B b ∧ C b a) (c2 : ∀ b, B b → ∃ a, A a ∧ C b a)
    (c3 : ∀ b a₁ a₂, C b a₁ → C b a₂ → a₁ = a₂)
    (c4 : ∀ a b₁ b₂, B b₁ → B b₂ → C b₁ a → C b₂ a → b₁ = b₂) :
    Nonempty ({a // A a} ≃ {b // B b}) := by
  classical
  let f : {a // A a} → {b // B b} := fun a =>
    ⟨Classical.choose (c1 a.1 a.2), (Classical.choose_spec (c1 a.1 a.2)).1⟩
  have hf : ∀ a : {a // A a}, C (f a).1 a.1 := fun a => (Classical.choose_spec (c1 a.1 a.2)).2
  refine ⟨Equiv.ofBijective f ⟨fun a₁ a₂ h => ?_, fun b => ?_⟩⟩
  · apply Subtype.ext
    have h1 := hf a₁
    rw [h] at h1
    exact c3 _ _ _ h1 (hf a₂)
  · obtain ⟨a, ha, hC⟩ := c2 b.1 b.2
    exact ⟨⟨a, ha⟩, Subtype.ext (c4 a _ _ (f ⟨a, ha⟩).2 b.2 (hf ⟨a, ha⟩) hC)⟩
end Formalism.FourierDecayAlt.P.A5x9
