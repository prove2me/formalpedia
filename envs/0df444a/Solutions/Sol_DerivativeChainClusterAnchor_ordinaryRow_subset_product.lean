-- Prove2me | solution 1 for DerivativeChainClusterAnchor.ordinaryRow_subset_product
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:12:37.431054+00:00
-- url     : https://prove2.me/submissions/7a559c5f-9c04-4386-b692-a7db4ad1780f

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Theorems.Thm_DerivativeChainClusterAnchor_iterate_derivative_slot_product
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






theorem solution {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    _root_.DerivativeChainClusterAnchor.ordinaryRow a m = C ((n.choose m:ℂ)⁻¹) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ∏ i ∈ S, (X-C (a i)) := by
  rw [_root_.DerivativeChainClusterAnchor.ordinaryRow,_root_.DerivativeChainClusterAnchor.sourcePolynomial,_root_.DerivativeChainClusterAnchor.iterate_derivative_slot_product a (by simpa using Nat.sub_le n m)]
  simp only [Finset.card_univ,Fintype.card_fin,Nat.sub_sub_self hm]
  rw [← mul_assoc, ← map_natCast (f := C), ← map_mul]
  congr 1
  apply congrArg C
  have hfac : (n.choose m:ℂ)*(m.factorial:ℂ)*((n-m).factorial:ℂ)=(n.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc : (n.choose m:ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hm
  field_simp
  linear_combination hfac
