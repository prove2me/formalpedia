-- Prove2me | solution 1 for CompactnessConjecture.kQuotient_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/0175570c-d28d-4356-a3a4-a73e36ca9c0d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_not_acyclic_of_eight_cycle_copy
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_not_acyclic
import Theorems.Thm_CompactnessConjecture_kGamma_quotient_injective

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient gammaGraph kTemplate f (kGammaCopy 0)
    (kGamma_quotient_injective hf 0)).comp gammaCycleCopy
end CompactnessConjecture
