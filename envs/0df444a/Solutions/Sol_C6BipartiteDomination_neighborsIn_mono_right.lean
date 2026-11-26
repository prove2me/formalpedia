-- Prove2me | solution 1 for C6BipartiteDomination.neighborsIn_mono_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:42.038387+00:00
-- url     : https://prove2.me/submissions/40c3f331-b833-49ef-8a8c-ff53f0c77950

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S T₁ T₂ : Finset V} (h : T₁ ⊆ T₂) :
    neighborsIn G S T₁ ⊆ neighborsIn G S T₂ := by
  classical
  intro w hw
  rw [mem_neighborsIn] at hw ⊢
  exact ⟨h hw.1, hw.2⟩
end C6BipartiteDomination
