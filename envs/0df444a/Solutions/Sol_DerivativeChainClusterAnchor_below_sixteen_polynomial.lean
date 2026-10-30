-- Prove2me | solution 1 for DerivativeChainClusterAnchor.below_sixteen_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:04:04.73539+00:00
-- url     : https://prove2.me/submissions/2f27d2c9-a23b-419c-b202-edccda35b30c

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
import Theorems.Thm_DerivativeChainClusterAnchor_baseline_complete_chain_radius
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
namespace DerivativeChainClusterAnchor
noncomputable section













theorem below_sixteen_complete_chain (n : ℕ) (a : Fin (n+1) → ℂ) (hn : n+1 < 16)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hsource : ∀ i, ‖a i-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ Real.sqrt (n:ℝ)*R ∧ (0 < R → chainCost z < 4*R) := by
  obtain ⟨z,hz,hcost⟩ := baseline_complete_chain_radius (by omega : 0 < n+1) a o R hR hsource
  have hcost' : chainCost z ≤ Real.sqrt (n:ℝ)*R := by simpa only [Nat.add_sub_cancel] using hcost
  have hnR : (n:ℝ) ≤ 14 := by exact_mod_cast (by omega : n ≤ 14)
  have hroot : Real.sqrt (n:ℝ) < 4 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),Real.sqrt_nonneg (n:ℝ)]
  exact ⟨z,hz,hcost',fun hpos => hcost'.trans_lt (mul_lt_mul_of_pos_right hroot hpos)⟩

end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor














theorem solution (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (hsmall : n < 16)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt ((n-1:ℕ):ℝ)*R ∧ (0 < R → _root_.DerivativeChainPrivate.chainCost z < 4*R) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨a,hpa,hmem,_⟩ := _root_.DerivativeChainClusterAnchor.actual_polynomial_slots p hp (n+1) hdegree (fun _ => True)
    obtain ⟨z,hz,hcost,hstrict⟩ := _root_.DerivativeChainClusterAnchor.below_sixteen_complete_chain n a hsmall o R hR
      (fun i => hsource (a i) (hmem i))
    refine ⟨z,?_,?_,hstrict⟩
    · intro i; rw [hpa]; exact hz i
    · simpa only [Nat.add_sub_cancel] using hcost
