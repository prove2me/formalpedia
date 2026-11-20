-- Prove2me | solution 1 for DeletionCode.ManuscriptCounting.inclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:06.764101+00:00
-- url     : https://prove2.me/submissions/c5a539b9-4409-4da9-84c5-438578a8de73

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting

set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex
namespace DeletionCode.ManuscriptCounting
theorem _root_.solution (t : ℕ) (x : Letters) (n k R c : ℕ) :
    Function.Injective (inclusion t x n k R c) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  exact congrArg (fun Q : {Q : RuleSet k //
    CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} => Q.val) h
end DeletionCode.ManuscriptCounting
