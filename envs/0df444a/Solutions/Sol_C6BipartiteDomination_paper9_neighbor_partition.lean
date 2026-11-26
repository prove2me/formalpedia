-- Prove2me | solution 1 for C6BipartiteDomination.paper9_neighbor_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:19.759829+00:00
-- url     : https://prove2.me/submissions/cbe64346-d0c8-41e8-aa38-4c9240cfc64e

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_PPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
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
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {u : V} (huB : u ∈ BPart G D) :
    (Finset.univ.filter fun q => G.Adj u q) =
      (D.filter fun q => G.Adj u q) ∪
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    have hadj : G.Adj u q := (Finset.mem_filter.mp hq).2
    by_cases hqD : q ∈ D
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqD, hadj⟩)
    · have hqWB : q ∈ WBPart G D := by
        rw [mem_WBPart]
        refine ⟨hqD, ?_⟩
        intro hq0
        exact ((mem_W0Part G D q).mp hq0).2 u huB hadj
      by_cases hqP : q ∈ PPart G D
      · rcases (mem_PPart G D q).mp hqP with ⟨b, hbB, hqPriv⟩
        have hbD := (mem_BPart G D b).mp hbB |>.1
        have hpriv := (mem_privateExternalNeighbors G D b q).mp hqPriv |>.2
        have hbu : b = u := ((hpriv u (mem_BPart G D u |>.mp huB |>.1)).mp
          hadj).symm
        subst b
        exact Finset.mem_union_right _ (Finset.mem_union_left _ hqPriv)
      · have hqS : q ∈ SPart G D := by
          rw [mem_SPart]
          exact ⟨hqWB, hqP⟩
        exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqS, hadj⟩))
  · intro hq
    rcases Finset.mem_union.mp hq with hqD | hqRest
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hqD).2⟩
    · rcases Finset.mem_union.mp hqRest with hqPriv | hqS
      · have hqInfo := (mem_privateExternalNeighbors G D u q).mp hqPriv
        have huD := (mem_BPart G D u).mp huB |>.1
        have hadj := (hqInfo.2 u huD).mpr rfl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      · have hadj := (Finset.mem_filter.mp hqS).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
end C6BipartiteDomination
