-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_jTemplate_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/1db90c48-af39-43bd-ba20-737fea94823f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
import Theorems.Thm_CompactnessConjecture_symplecticLine_char_two_pair_avoidance

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]
namespace CompactnessConjecture
theorem _root_.solution
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {vertex | InJCopy copy vertex}) :
    False :=
  symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    K (symplecticLine_char_two_pair_avoidance K) hom hbase hcopies
end CompactnessConjecture
