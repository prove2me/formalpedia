-- Prove2me | solution 1 for C6BipartiteDomination.paper11_k3_k4_supports_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:04.514496+00:00
-- url     : https://prove2.me/submissions/9b977951-abe2-4751-b1d1-c11dcaab9ae7

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} :
    Disjoint (paper11K3Supports G D) (paper11K4Supports G D) := by
  rw [Finset.disjoint_left]
  intro w hw3 hw4
  have h3 := (Finset.mem_filter.mp hw3).2
  have h4 := (Finset.mem_filter.mp hw4).2
  omega
end C6BipartiteDomination
