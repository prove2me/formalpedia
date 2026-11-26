-- Prove2me | solution 1 for C6BipartiteDomination.privateExternal_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:30.053987+00:00
-- url     : https://prove2.me/submissions/4724afb6-1204-49e7-8272-0afda1fc0a2b

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    (BPart G D : Set V).PairwiseDisjoint (privateExternalNeighbors G D) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro b hb c hc hne
  have hbInfo := (mem_BPart G D b).mp hb
  have hcInfo := (mem_BPart G D c).mp hc
  rcases hne with ⟨w, hw⟩
  have hwBC := Finset.mem_inter.mp hw
  have hwB : w ∈ privateExternalNeighbors G D b := hwBC.1
  have hwC : w ∈ privateExternalNeighbors G D c := hwBC.2
  have hbPriv := (mem_privateExternalNeighbors G D b w).mp hwB |>.2
  have hcPriv := (mem_privateExternalNeighbors G D c w).mp hwC |>.2
  have hadjB : G.Adj b w := (hbPriv b hbInfo.1).mpr rfl
  exact (hcPriv b hbInfo.1).mp hadjB
end C6BipartiteDomination
