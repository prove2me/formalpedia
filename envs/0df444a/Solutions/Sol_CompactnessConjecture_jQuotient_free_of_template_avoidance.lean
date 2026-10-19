-- Prove2me | solution 1 for CompactnessConjecture.jQuotient_free_of_template_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/91341700-0b08-4d76-a363-d433c1af2a7c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} (host : SimpleGraph V)
    (havoid : ∀ hom : jTemplate →g host,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (quotientGraph jTemplate f).Free host := by
  rintro ⟨copy⟩
  let hom : jTemplate →g host :=
    copy.toHom.comp (jQuotientProjectionHom hf)
  apply havoid hom
  · intro first second heq
    change
      copy (⟨f (.inl (.inl first)),
        .inl (.inl first), rfl⟩ : Set.range f) =
        copy (⟨f (.inl (.inl second)),
          .inl (.inl second), rfl⟩ : Set.range f)
      at heq
    apply hf.2.1
    exact congrArg Subtype.val (copy.injective heq)
  · intro index first hfirst second hsecond heq
    change
      copy (⟨f first, first, rfl⟩ : Set.range f) =
        copy (⟨f second, second, rfl⟩ : Set.range f)
      at heq
    apply hf.2.2 index hfirst hsecond
    exact congrArg Subtype.val (copy.injective heq)
end CompactnessConjecture
