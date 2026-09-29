-- Prove2me | solution 1 for Erdos180.proposedFamily_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:26:07.314575+00:00
-- url     : https://prove2.me/submissions/1ad743d6-1174-4369-83d2-220285374a48

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum

namespace Erdos180

noncomputable section
open Finset SimpleGraph

theorem jQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ jQuotients ↔
      ∃ f : JVertex → JVertex, JAdmissible f ∧
        encodeFiniteGraph (quotientGraph jTemplate f) = graph := by
  rw [jQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

theorem kQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by
  rw [kQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

end

end Erdos180

open Erdos180
open Finset SimpleGraph

theorem solution {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by
  classical
  simp only [proposedFamily, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, jQuotients_mem_iff, kQuotients_mem_iff]
