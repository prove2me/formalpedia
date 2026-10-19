-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/2182484d-2d46-4495-87fe-7490bac66ffd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_jQuotients_mem_iff
import Theorems.Thm_CompactnessConjecture_kQuotients_mem_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by
  classical
  simp only [proposedFamily, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, jQuotients_mem_iff, kQuotients_mem_iff]
end CompactnessConjecture
