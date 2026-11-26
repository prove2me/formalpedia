-- Prove2me | solution 1 for C6BipartiteDomination.Z0_disjoint_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:46.075538+00:00
-- url     : https://prove2.me/submissions/aa24faa8-ddbf-45de-a58b-570b62a3dae3

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} :
    Disjoint (Z0Part G D) (BPart G D) := by
  rw [Finset.disjoint_left]
  intro z hz0 hb
  have hz := (mem_Z0Part G D z).mp hz0 |>.1
  exact (mem_BPart G D z).mp hb |>.2 hz
end C6BipartiteDomination
