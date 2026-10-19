-- Prove2me | solution 1 for CompactnessConjecture.kQuotients_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/870d2ed7-5599-47a2-9133-b96e183c275c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by
  rw [kQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩
end CompactnessConjecture
