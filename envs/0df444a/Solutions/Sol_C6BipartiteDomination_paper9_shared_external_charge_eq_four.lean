-- Prove2me | solution 1 for C6BipartiteDomination.paper9_shared_external_charge_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:44.750111+00:00
-- url     : https://prove2.me/submissions/eab35104-baaf-458d-97f0-c56d37ca2b2f

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile
import Theorems.Thm_C6BipartiteDomination_paper9_shared_beta_eq_one

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    externalCharge G D q = 4 := by
  have hprof := paper9_shared_compensation_profile G hX huB hq
  have hβ := paper9_shared_beta_eq_one G hX huB hq
  unfold externalCharge
  rw [hprof.2.2, hβ]
  norm_num
end C6BipartiteDomination
