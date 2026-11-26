-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.paired_balance_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:39.944881+00:00
-- url     : https://prove2.me/submissions/1ea0daaa-1621-4eb4-ba9c-6029509c5fa6

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_balance_identity

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (p : Vec n) :
    dot (Fin.append p (1 - p)) (values a) - dot (values a) 1 / 2 =
      4 * (base a : ℝ) ^ (2 * n) *
        (dot p (fun i => (a i : ℝ)) - (∑ i, (a i : ℝ)) / 2) := by
  rw [balance_identity]
  simp only [dot, mul_sub, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.one_apply]
  ring
end CSeparatedNPComplete.SquareReduction
