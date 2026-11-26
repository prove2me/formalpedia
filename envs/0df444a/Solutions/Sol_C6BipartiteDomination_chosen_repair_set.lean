-- Prove2me | solution 1 for C6BipartiteDomination.chosen_repair_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:03.718064+00:00
-- url     : https://prove2.me/submissions/05532481-309f-4d69-a925-b955da1f46c0

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
import Theorems.Thm_C6BipartiteDomination_chosen_repairs_beta_two
import Theorems.Thm_C6BipartiteDomination_chosen_repair_beta_three
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification


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
    ∃ R : Finset V,
      (∀ u, ChosenRepairRelation G D w R u → IsRepairVertex G D w u) ∧
      ((kCharge G D w = 3 ∧ R.card = 2) ∨
       (kCharge G D w = 4 ∧ R.card = 2) ∨
       (kCharge G D w = 3 ∧ R.card = 1)) := by
  classical
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with
    ⟨hk, hβ⟩ | ⟨hk, hβ⟩ | ⟨hk, hβ⟩
  · obtain ⟨R, hcard, hR⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    refine ⟨R, ?_, Or.inl ⟨hk, hcard⟩⟩
    intro u hChosen
    exact hR u hChosen.1
  · obtain ⟨u, hu⟩ := chosen_repair_beta_three G hCan hw hβ
    refine ⟨{u}, ?_, Or.inr (Or.inr ⟨hk, by simp⟩)⟩
    intro v hChosen
    have hEq : v = u := Finset.mem_singleton.mp hChosen.1
    simpa [hEq] using hu
  · obtain ⟨R, hcard, hR⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    refine ⟨R, ?_, Or.inr (Or.inl ⟨hk, hcard⟩)⟩
    intro u hChosen
    exact hR u hChosen.1
end C6BipartiteDomination
