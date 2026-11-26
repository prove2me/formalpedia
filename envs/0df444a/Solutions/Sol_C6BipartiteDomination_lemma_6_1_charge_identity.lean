-- Prove2me | solution 1 for C6BipartiteDomination.lemma_6_1_charge_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:13.895907+00:00
-- url     : https://prove2.me/submissions/4358d882-d87b-487b-bdf4-1e70752b24fe

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_wb_card_eq
import Theorems.Thm_C6BipartiteDomination_sum_beta_eq_sum_s
import Theorems.Thm_C6BipartiteDomination_lemma_6_1_charge_identity_of_counts

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by
  apply lemma_6_1_charge_identity_of_counts G D (wb_card_eq G D hCan)
  exact sum_beta_eq_sum_s G D
end C6BipartiteDomination
