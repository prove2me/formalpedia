-- Prove2me | solution 1 for DeletionCode.CountingLemma.exists_counting_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:21.098367+00:00
-- url     : https://prove2.me/submissions/abfa4803-7943-441d-8d75-400715165cf4

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
import Theorems.Thm_DeletionCode_CountingLemma_counting_generating_sets
import Theorems.Thm_DeletionCode_CountExponent_exponent_pos


set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent
namespace DeletionCode.CountingLemma
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters) (n k R c : ℕ),
      1 ≤ R → KUnique x n k → ∀ group : Fin (2 * t * R) → Fin R,
        Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) := by
  exact ⟨exponent t, exponent_pos t ht, fun x n k R c hR hx group =>
    counting_generating_sets t ht x n k R c hR hx group⟩
end DeletionCode.CountingLemma
