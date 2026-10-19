-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_encoded_kQuotient_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/d4671975-dcb1-4719-8207-6524122a3e4d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_kQuotient_of_odd
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_encodeFiniteGraph_free_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  (symplecticQuadrangle_encodeFiniteGraph_free_iff K
    (quotientGraph kTemplate f)).mpr
    (symplecticQuadrangle_no_kQuotient_of_odd K htwo hf)
end CompactnessConjecture
