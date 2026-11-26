-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3SpecialBudget_card_le_Qstar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:55.566373+00:00
-- url     : https://prove2.me/submissions/ffeaaa9b-4e06-4388-b1b3-21e299624704

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_special_witness_owner_unique_of_eq
import Theorems.Thm_C6BipartiteDomination_paper11_special_witness_for_budget_vertex

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11K3SpecialBudgetVertices G D hCan hmax).card ≤
      (paper10SpecialQSet G hCan hmax).card := by
  classical
  let P := paper11K3SpecialBudgetVertices G D hCan hmax
  let Q := paper10SpecialQSet G hCan hmax
  let f : {u : V // u ∈ P} → {q : V // q ∈ Q} := fun x => by
    let hspec := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := x.1) x.2
    exact ⟨Classical.choose hspec, (Classical.choose_spec hspec).1⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hspecA := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := a.1) a.2
    have hspecB := paper11_special_witness_for_budget_vertex G hCan hmax
      (u := b.1) b.2
    obtain ⟨da, hda⟩ := (Classical.choose_spec hspecA).2
    obtain ⟨db, hdb⟩ := (Classical.choose_spec hspecB).2
    have hq : Classical.choose hspecA = Classical.choose hspecB := by
      change (f a).1 = (f b).1
      exact congrArg Subtype.val hab
    have howner := paper11_special_witness_owner_unique_of_eq G hCan hmax
      hq da db
    rw [hda, hdb] at howner
    exact Subtype.ext howner
  have hcard := Finset.card_le_card_of_injective hinj
  simpa [P, Q] using hcard
end C6BipartiteDomination
