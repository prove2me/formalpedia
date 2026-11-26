-- Prove2me | solution 1 for C6BipartiteDomination.neighborsIn_mono_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:22.737803+00:00
-- url     : https://prove2.me/submissions/43086a8f-4eb9-4a2d-9ece-b9e1d7c1d791

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S₁ S₂ T : Finset V} (h : S₁ ⊆ S₂) :
    neighborsIn G S₁ T ⊆ neighborsIn G S₂ T := by
  classical
  intro w hw
  rw [mem_neighborsIn] at hw ⊢
  refine ⟨hw.1, ?_⟩
  rcases hw.2 with ⟨v, hv, hadj⟩
  exact ⟨v, h hv, hadj⟩
end C6BipartiteDomination
