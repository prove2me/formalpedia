-- Prove2me | solution 1 for CompactnessConjecture.jQuotient_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/b1b8dcf6-189a-4c5a-bda0-f900beb70464

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_not_acyclic_of_eight_cycle_copy
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_not_acyclic
import Theorems.Thm_CompactnessConjecture_jTheta_quotient_injective

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient thetaGraph jTemplate f (jThetaCopy 0)
    (jTheta_quotient_injective hf 0)).comp thetaCycleCopy
end CompactnessConjecture
