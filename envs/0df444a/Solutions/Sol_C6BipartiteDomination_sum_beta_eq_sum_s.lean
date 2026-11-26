-- Prove2me | solution 1 for C6BipartiteDomination.sum_beta_eq_sum_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:03.701942+00:00
-- url     : https://prove2.me/submissions/dcf1df0b-0c97-477f-8168-597c89d314f3

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_sum_degreeTo_symm

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b := by
  exact sum_degreeTo_symm G (SPart G D) (BPart G D)
end C6BipartiteDomination
