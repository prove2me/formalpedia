-- Prove2me | solution 1 for C6BipartiteDomination.PPart_subset_WBPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:12.216809+00:00
-- url     : https://prove2.me/submissions/954f7b2a-7b99-4769-8eb9-e4e14cbf6389

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_PPart
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) : PPart G D ⊆ WBPart G D := by
  classical
  intro w hw
  rcases (mem_PPart G D w).mp hw with ⟨b, hb, hbw⟩
  have hbD := (mem_BPart G D b).mp hb |>.1
  have hp := (mem_privateExternalNeighbors G D b w).mp hbw
  rw [mem_WBPart]
  refine ⟨hp.1, ?_⟩
  intro hw0
  have hw0info := (mem_W0Part G D w).mp hw0
  exact hw0info.2 b hb (hp.2 b hbD |>.mpr rfl)
end C6BipartiteDomination
