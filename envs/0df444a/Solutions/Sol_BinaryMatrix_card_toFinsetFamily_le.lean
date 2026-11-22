-- Prove2me | solution 1 for BinaryMatrix.card_toFinsetFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:26.048518+00:00
-- url     : https://prove2.me/submissions/16d37670-59ee-41c8-81bc-8507e2684a13

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix
namespace BinaryMatrix
theorem _root_.solution {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.toFinsetFamily.vcDim ≤ d) :
    M.toFinsetFamily.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  calc M.toFinsetFamily.card
      _ ≤ M.toFinsetFamily.shatterer.card := card_le_card_shatterer _
      _ ≤ ∑ k ∈ Iic M.toFinsetFamily.vcDim, (Fintype.card (Fin n)).choose k :=
          card_shatterer_le_sum_vcDim
      _ = ∑ k ∈ Iic M.toFinsetFamily.vcDim, n.choose k := by
          simp [Fintype.card_fin]
      _ ≤ ∑ k ∈ Iic d, n.choose k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.mpr hd)
            (fun _ _ _ => Nat.zero_le _)
end BinaryMatrix
