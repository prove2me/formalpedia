-- Prove2me | solution 1 for DeletionCode.CountingLemma.counting_generating_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:12.693671+00:00
-- url     : https://prove2.me/submissions/a7015367-2b66-4962-a73b-c828a9638fcd

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_record_bound
import Theorems.Thm_DeletionCode_CountExponent_field_power_bound


set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent
namespace DeletionCode.CountingLemma
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R c : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k)
    (group : Fin (2 * t * R) → Fin R) :
    Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
      n ^ c * (windowLength k * R) ^ (exponent t * R) := by
  have hν : 1 ≤ 2 * t * R := by nlinarith
  exact (generatingSet_record_bound x n k (2 * t * R) R c group hν hx).trans
    (Nat.mul_le_mul_left (n ^ c) (field_power_bound k t R hR))
end DeletionCode.CountingLemma
