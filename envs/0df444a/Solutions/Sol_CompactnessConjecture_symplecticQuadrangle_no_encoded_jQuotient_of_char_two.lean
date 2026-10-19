-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_encoded_jQuotient_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/459c70ef-678e-4e67-9184-90e692cd3e80

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_jTemplate_of_char_two

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]
namespace CompactnessConjecture
theorem _root_.solution
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance K
    (symplecticQuadrangle_no_jTemplate_of_char_two K) hf
end CompactnessConjecture
