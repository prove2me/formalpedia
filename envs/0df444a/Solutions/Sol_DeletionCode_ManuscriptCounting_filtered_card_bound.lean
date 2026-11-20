-- Prove2me | solution 1 for DeletionCode.ManuscriptCounting.filtered_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:53.930961+00:00
-- url     : https://prove2.me/submissions/09e60d57-c63b-4459-b5f0-26ffecbdffad

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
import Theorems.Thm_DeletionCode_ManuscriptCounting_generatingSet_finite
import Theorems.Thm_DeletionCode_ManuscriptCounting_card_bound
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite


set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex
namespace DeletionCode.ManuscriptCounting
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) (P : RuleSet k → Prop) :
    Nat.card {Q : RuleSet k // GeneratingSet t x n k R c Q ∧ P Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) := by
  let : Finite {Q : RuleSet k // GeneratingSet t x n k R c Q} :=
    generatingSet_finite t ht x n k R c hR hx
  let forget : {Q : RuleSet k // GeneratingSet t x n k R c Q ∧ P Q} →
      {Q : RuleSet k // GeneratingSet t x n k R c Q} := fun Q => ⟨Q.val, Q.property.1⟩
  have hinj : Function.Injective forget := by
    intro Q₁ Q₂ h
    apply Subtype.ext
    exact congrArg (fun Q : {Q : RuleSet k // GeneratingSet t x n k R c Q} => Q.val) h
  exact (Nat.card_le_card_of_injective forget hinj).trans (card_bound t ht x n k R c hR hx)
end DeletionCode.ManuscriptCounting
