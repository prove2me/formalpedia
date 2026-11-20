-- Prove2me | solution 1 for DeletionCode.WitnessCounting.partition_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:30:34.80839+00:00
-- url     : https://prove2.me/submissions/13782fa1-dd84-4736-9f7f-3c2faa5eef1c

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators
namespace DeletionCode.WitnessCounting
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (x : Letters)
    (n k R : ℕ) (hR : 1 ≤ R) :
    Function.Injective (partition t ht x n k R hR) := by
  intro U V h
  apply Subtype.ext
  exact congrArg (fun z : IndexedSets t x n k R => z.2.val) h
end DeletionCode.WitnessCounting
