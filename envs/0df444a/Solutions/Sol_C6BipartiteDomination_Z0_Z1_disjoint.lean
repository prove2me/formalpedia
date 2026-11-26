-- Prove2me | solution 1 for C6BipartiteDomination.Z0_Z1_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:51.688473+00:00
-- url     : https://prove2.me/submissions/c5d6997f-6874-4563-96ee-5b7c5b384529

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_Z1Part

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    Disjoint (Z0Part G D) (Z1Part G D) := by
  rw [Finset.disjoint_left]
  intro z hz0 hz1
  have h0 := (mem_Z0Part G D z).mp hz0
  obtain ⟨_, w, hw, hAdj⟩ := (mem_Z1Part G D z).mp hz1
  exact h0.2 w hw hAdj
end C6BipartiteDomination
