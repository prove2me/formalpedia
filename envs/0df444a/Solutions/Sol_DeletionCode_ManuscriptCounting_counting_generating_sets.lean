-- Prove2me | solution 1 for DeletionCode.ManuscriptCounting.counting_generating_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:54.46295+00:00
-- url     : https://prove2.me/submissions/a931633b-32de-4fa5-9015-db3144e7d6ac

import Definitions.Def_DeletionCode_CountingLemma
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_ManuscriptCounting
import Theorems.Thm_DeletionCode_ManuscriptCounting_card_bound
import Theorems.Thm_DeletionCode_CountExponent_exponent_pos


set_option autoImplicit true
open DeletionCode DeletionCode.ManuscriptCounting
open Windows HeaderRecovery CatalogueWords CatalogueBridge SignedSupport
open RuleReconstruction RuleSetGraph SignedRuleCount CountExponent CanonicalIndex
namespace DeletionCode.ManuscriptCounting
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters) (n k R c : ℕ),
      1 ≤ R → KUnique x n k →
        Nat.card {Q : RuleSet k // GeneratingSet t x n k R c Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) := by
  exact ⟨exponent t, exponent_pos t ht,
    fun x n k R c hR hx => card_bound t ht x n k R c hR hx⟩
end DeletionCode.ManuscriptCounting
