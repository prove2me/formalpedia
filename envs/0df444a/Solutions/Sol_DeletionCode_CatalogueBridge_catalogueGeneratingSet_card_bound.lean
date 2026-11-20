-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.catalogueGeneratingSet_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:43.347277+00:00
-- url     : https://prove2.me/submissions/93252374-5b4b-43bb-9fb0-471c948e3710

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
import Theorems.Thm_DeletionCode_CatalogueBridge_catalogueGeneratingSet_included
import Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_card_bound
import Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_finite


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
theorem _root_.solution (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by
  let : Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    generatingRuleSet_finite x n k ν R c group hν hx
  let inclusion : {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} →
      {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} :=
    fun Q => ⟨Q.val, catalogueGeneratingSet_included x n k ν R t c group Q.val Q.property⟩
  have hinj : Function.Injective inclusion := by
    intro Q₁ Q₂ heq
    apply Subtype.ext
    exact congrArg (fun Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} => Q.val) heq
  exact (Nat.card_le_card_of_injective inclusion hinj).trans
    (generatingRuleSet_card_bound x n k ν R c group hν hx)
end DeletionCode.CatalogueBridge
