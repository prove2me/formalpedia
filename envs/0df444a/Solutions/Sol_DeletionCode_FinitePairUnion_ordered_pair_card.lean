-- Prove2me | solution 1 for DeletionCode.FinitePairUnion.ordered_pair_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:30.141201+00:00
-- url     : https://prove2.me/submissions/6fde187f-f4a2-4e83-ad63-51c818031887

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Definitions.Def_DeletionCode_FinitePairUnion

set_option autoImplicit true
open DeletionCode DeletionCode.FinitePairUnion
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
namespace DeletionCode.FinitePairUnion
theorem _root_.solution (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]
end DeletionCode.FinitePairUnion
