-- Prove2me | solution 1 for DeletionCode.WitnessCounting.candidate_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:33:50.826438+00:00
-- url     : https://prove2.me/submissions/3d490fee-e24a-4e2f-a17a-f21f3681bfc1

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
import Theorems.Thm_DeletionCode_WitnessCounting_partition_injective
import Theorems.Thm_DeletionCode_CountingLemma_generatingSet_finite
import Theorems.Thm_DeletionCode_ManuscriptCounting_generatingSet_finite


set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators
namespace DeletionCode.WitnessCounting
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) (hx : KUnique x n k) :
    Finite {U : RuleSet k // Candidate t x n k R U} := by
  let : ∀ c : ComponentIndex t k R,
      Finite {U : RuleSet k // GeneratingSet t x n k R c.val.val U} :=
    fun c => generatingSet_finite t ht x n k R c.val.val hR hx
  let : Finite (IndexedSets t x n k R) := by unfold IndexedSets; infer_instance
  exact Finite.of_injective (partition t ht x n k R hR)
    (partition_injective t ht x n k R hR)
end DeletionCode.WitnessCounting
