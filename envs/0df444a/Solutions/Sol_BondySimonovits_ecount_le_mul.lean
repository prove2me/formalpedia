-- Prove2me | solution 1 for BondySimonovits.ecount_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:40.253011+00:00
-- url     : https://prove2.me/submissions/545ed4bc-1bb5-4211-9fc3-9b066d7dda55

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
omit [DecidableEq V]
namespace BondySimonovits
theorem _root_.solution (A B : Finset V) : ecount K A B ≤ A.card * B.card := by
  unfold ecount
  calc ∑ a ∈ A, (B.filter (K.Adj a)).card ≤ ∑ _a ∈ A, B.card :=
        Finset.sum_le_sum (fun a _ => Finset.card_filter_le _ _)
    _ = A.card * B.card := by rw [Finset.sum_const, smul_eq_mul]
end BondySimonovits
