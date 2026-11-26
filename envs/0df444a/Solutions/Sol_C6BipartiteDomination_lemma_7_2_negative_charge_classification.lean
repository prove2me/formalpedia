-- Prove2me | solution 1 for C6BipartiteDomination.lemma_7_2_negative_charge_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:03.730257+00:00
-- url     : https://prove2.me/submissions/464bac31-e227-4940-8085-4c078ed2f68a

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_beta_pos_of_mem_SPart
import Theorems.Thm_C6BipartiteDomination_beta_ge_two_of_k_ge_two
import Theorems.Thm_C6BipartiteDomination_support_union_card_le_degree

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2) := by
  have hβpos := beta_pos_of_mem_SPart G hw
  have hk : 2 ≤ kCharge G D w := by
    by_contra h
    have hkle : kCharge G D w ≤ 1 := by omega
    unfold externalCharge at ha
    push_cast at ha
    omega
  have hβtwo := beta_ge_two_of_k_ge_two G hCan hw hk
  have hsum := support_union_card_le_degree G (D := D) (w := w)
  have hbound : kCharge G D w + betaCharge G D w ≤ 6 := by
    exact hsum.trans (hmax w)
  have hneg : 8 + 3 * betaCharge G D w < 7 * kCharge G D w := by
    unfold externalCharge at ha
    push_cast at ha
    omega
  omega
end C6BipartiteDomination
