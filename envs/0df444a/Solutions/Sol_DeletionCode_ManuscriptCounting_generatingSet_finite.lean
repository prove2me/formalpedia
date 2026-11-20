-- Prove2me | solution 1 for DeletionCode.ManuscriptCounting.generatingSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:30.380871+00:00
-- url     : https://prove2.me/submissions/29ad6ecd-5364-419c-b2e3-2dd6899e0a7b

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
import Theorems.Thm_DeletionCode_ManuscriptCounting_inclusion_injective
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite


set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex
namespace DeletionCode.ManuscriptCounting
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingSet t x n k R c Q} := by
  let : Finite {Q : RuleSet k //
      CountingLemma.GeneratingSet x n k (2 * t * R) R c (group t R) Q} :=
    CountingLemma.generatingSet_finite x n k (2 * t * R) R c (group t R)
      (by nlinarith) hx
  exact Finite.of_injective (inclusion t x n k R c) (inclusion_injective t x n k R c)
end DeletionCode.ManuscriptCounting
