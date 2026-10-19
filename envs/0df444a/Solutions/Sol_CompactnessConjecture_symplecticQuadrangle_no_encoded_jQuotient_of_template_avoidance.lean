-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/6e6296b4-7209-4888-9236-90ce96ba04c2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_encodeFiniteGraph_free_iff
import Theorems.Thm_CompactnessConjecture_jQuotient_free_of_template_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    (K : Type*) [Field K]
    (havoid : ∀ hom : jTemplate →g symplecticQuadrangle K,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) := by
  exact
    (symplecticQuadrangle_encodeFiniteGraph_free_iff K
      (quotientGraph jTemplate f)).mpr
      (jQuotient_free_of_template_avoidance
        (symplecticQuadrangle K) havoid hf)
end CompactnessConjecture
