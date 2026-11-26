-- Prove2me | solution 1 for C6BipartiteDomination.paper9_neighbor_partition_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:22.503827+00:00
-- url     : https://prove2.me/submissions/de8af5ad-3b12-4952-b12f-165a8305746e

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_mem_PPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {u : V} (huB : u ∈ BPart G D) :
    Disjoint (D.filter fun q => G.Adj u q)
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) ∧
    Disjoint (privateExternalNeighbors G D u)
        ((SPart G D).filter fun q => G.Adj u q) := by
  classical
  constructor
  · rw [Finset.disjoint_left]
    intro q hqD hqR
    rcases Finset.mem_union.mp hqR with hqP | hqS
    · exact (mem_privateExternalNeighbors G D u q).mp hqP |>.1
        ((Finset.mem_filter.mp hqD).1)
    · have hqWB := (mem_SPart G D q).mp (Finset.mem_filter.mp hqS).1 |>.1
      exact (mem_WBPart G D q).mp hqWB |>.1 ((Finset.mem_filter.mp hqD).1)
  · rw [Finset.disjoint_left]
    intro q hqP hqS
    have hqInP : q ∈ PPart G D := by
      apply (mem_PPart G D q).mpr
      exact ⟨u, huB, hqP⟩
    exact (mem_SPart G D q).mp (Finset.mem_filter.mp hqS).1 |>.2 hqInP
end C6BipartiteDomination
