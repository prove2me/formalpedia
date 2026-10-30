-- Prove2me | solution 1 for DerivativeChainClusterAnchor.iterate_derivative_slot_product
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:10:50.08535+00:00
-- url     : https://prove2.me/submissions/df52f20e-912a-409e-a064-1a9faa7f94cd

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial Finset
open DerivativeChainClusterAnchor


-- Slot indices retain coincident root values as separate factors.
-- The proof extends Mathlib's iterate_derivative_prod_X_sub_C to a noninjective root map.
theorem solution {ι : Type} [DecidableEq ι]
    (a : ι → ℂ) {S : Finset ι} {k : ℕ} (hk : k ≤ S.card) :
    derivative^[k] (∏ i ∈ S, (X-C (a i))) =
      (k.factorial : ℂ[X]) * ∑ T ∈ S.powersetCard (S.card-k), ∏ i ∈ T, (X-C (a i)) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    specialize ih (Nat.le_of_succ_le hk)
    nth_rewrite 1 [add_comm]
    rw [Function.iterate_add_apply, Function.iterate_one, ih, ← nsmul_eq_mul,
      derivative_smul, nsmul_eq_mul, derivative_sum, Nat.factorial_succ,
      mul_comm (k+1), Nat.cast_mul, mul_assoc]
    congr 1
    calc
      ∑ T ∈ S.powersetCard (S.card-k), derivative (∏ i ∈ T, (X-C (a i))) =
          ∑ T ∈ S.powersetCard (S.card-k), ∑ i ∈ T, ∏ j ∈ T.erase i, (X-C (a j)) := by
        congr! with T hT
        simp_rw [derivative_prod_finset, derivative_X_sub_C, mul_one]
      _ = ∑ (T ∈ S.powersetCard (S.card-k)) (i ∈ S) with i ∈ T,
          ∏ j ∈ T.erase i, (X-C (a j)) := by
        rw [← sum_finset_product']
        grind
      _ = ∑ (T ∈ S.powersetCard (S.card-(k+1))) (i ∈ S) with i ∉ T,
          ∏ j ∈ T, (X-C (a j)) := by
        apply sum_bij' (fun ⟨T,i⟩ _ => ⟨T.erase i,i⟩) (fun ⟨T,i⟩ _ => ⟨insert i T,i⟩)
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        all_goals grind
      _ = ∑ T ∈ S.powersetCard (S.card-(k+1)), ∑ i ∈ S \ T,
          ∏ j ∈ T, (X-C (a j)) := by
        rw [← sum_finset_product']
        grind
      _ = (k+1) * ∑ T ∈ S.powersetCard (S.card-(k+1)), ∏ j ∈ T, (X-C (a j)) := by
        rw [mul_sum]
        congr! 1 with T hT
        simp [sum_const, show (S \ T).card=k+1 by grind]
      _ = _ := by grind
