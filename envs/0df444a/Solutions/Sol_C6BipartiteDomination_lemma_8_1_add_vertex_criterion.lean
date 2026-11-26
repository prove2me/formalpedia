-- Prove2me | solution 1 for C6BipartiteDomination.lemma_8_1_add_vertex_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:20.524893+00:00
-- url     : https://prove2.me/submissions/9f562366-244d-4f03-bf41-a39d971570c5

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
import Theorems.Thm_C6BipartiteDomination_bipartite_add_of_uniform_neighbors

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {B : Finset V} {w : V} (hwB : w ∉ B) :
    IsBipartiteOn G (B ∪ {w}) ↔
      ∃ c : V → Bool, ∃ c₀ : Bool,
        (∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v) ∧
        ∀ v ∈ B, G.Adj w v → c v = c₀ := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, !c w, ?_⟩
    constructor
    · intro u v hu hv hadj
      exact hc (Finset.mem_union_left _ hu) (Finset.mem_union_left _ hv) hadj
    · intro v hv hadj
      have hne : c v ≠ c w := hc (Finset.mem_union_left _ hv)
        (Finset.mem_union_right B (Finset.mem_singleton_self w)) hadj.symm
      cases hcv : c v <;> cases hcw : c w <;> simp_all
  · rintro ⟨c, c₀, hc, huniform⟩
    exact bipartite_add_of_uniform_neighbors G
      (B := B) (S := B) Finset.Subset.rfl hwB c hc c₀ huniform
end C6BipartiteDomination
