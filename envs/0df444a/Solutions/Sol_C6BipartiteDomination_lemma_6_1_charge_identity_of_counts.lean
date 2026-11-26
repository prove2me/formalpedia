-- Prove2me | solution 1 for C6BipartiteDomination.lemma_6_1_charge_identity_of_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:40.520477+00:00
-- url     : https://prove2.me/submissions/86f59a40-b5d7-41df-b280-7012d5847322

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    (D : Finset V)
    (hWB : (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card)
    (hInc : (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by
  classical
  unfold vertexCharge externalCharge incidenceTotal
  have hIncZ := congrArg (fun n : ℕ => (n : ℤ)) hInc
  have hWBZ := congrArg (fun n : ℕ => (n : ℤ)) hWB
  push_cast at hIncZ hWBZ ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul] at *
  simp_rw [← Finset.mul_sum] at *
  linarith [hWBZ, hIncZ]
end C6BipartiteDomination
