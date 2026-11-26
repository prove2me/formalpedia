-- Prove2me | solution 1 for C6BipartiteDomination.nonisolated_of_mem_BPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:33.982097+00:00
-- url     : https://prove2.me/submissions/019c2c1b-dd4d-462e-8d0a-55944fd5c234

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_ZPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} {b : V}
    (hb : b ∈ BPart G D) : NonisolatedIn G D b := by
  classical
  have hbInfo := (mem_BPart G D b).mp hb
  refine ⟨hbInfo.1, ?_⟩
  by_contra h
  apply hbInfo.2
  rw [mem_ZPart]
  exact ⟨hbInfo.1, by
    intro u hu hadj
    exact h ⟨u, hu, hadj⟩⟩
end C6BipartiteDomination
