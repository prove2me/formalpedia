-- Prove2me | solution 1 for C6BipartiteDomination.lemma_8_5_compensation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:26.34337+00:00
-- url     : https://prove2.me/submissions/8e8d07de-f4e1-4498-b7ee-cb327bed7584

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_lemma_8_4_compensation_decomposition
import Theorems.Thm_C6BipartiteDomination_lemma_8_5_independent_set_lower_bound
import Theorems.Thm_C6BipartiteDomination_private_card_eq_two_add_x


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
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    kCharge G D w - 2 ≤
      xCharge G D u + (sharedCompensation G D (supportX G D w) u).card := by
  classical
  have hInd := lemma_8_5_independent_set_lower_bound G hCan hmax hw ha hChosen
  obtain ⟨J, hJQ, hJind, hJlarge⟩ := hInd
  have hDec := lemma_8_4_compensation_decomposition G hCan hChosen
  have huB := hChosen.2.1
  have hPrivate := private_card_eq_two_add_x G hCan huB
  have hQcard : kCharge G D w ≤
      (compensationRegion G D (supportX G D w) u w).card := by
    exact hJlarge.trans (Finset.card_le_card hJQ)
  have hsum : kCharge G D w ≤
      (privateCompensation G D u).card +
        (sharedCompensation G D (supportX G D w) u).card := by
    rw [hDec.1, Finset.card_union_of_disjoint hDec.2.1] at hQcard
    exact hQcard
  have hPrivate' : (privateCompensation G D u).card = 2 + xCharge G D u := by
    simpa [privateCompensation] using hPrivate
  rw [hPrivate'] at hsum
  omega
end C6BipartiteDomination
