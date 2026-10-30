-- Prove2me | solution 1 for DerivativeChainExtremal.radial_prefix_centroid_four
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:12:29.920683+00:00
-- url     : https://prove2.me/submissions/84119a1b-a330-48c6-8fa8-4fde5252bf4c

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_polynomial_radial_prefix
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

theorem solution (p : Polynomial ℂ)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ : ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q)
    (ha : ∀ w : ℂ, p.eval w=0 → ‖w‖ ≤ 1)
    (hbudget : ((n+1-m+1:ℕ):ℝ)*(1-‖_root_.DerivativeChainContinuation.rootCentroid p‖^2) ≤ 16) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=_root_.DerivativeChainContinuation.rootCentroid p ∧ _root_.DerivativeChainPrivate.chainCost z ≤ 4 := by
  obtain ⟨z,hzr,hz0,hzc⟩ := _root_.DerivativeChainExtremal.polynomial_radial_prefix p n m k r hdegree q σ C₀ 0 1
    hm hmn hk hr hq hC hσ hcore (by norm_num) (by simpa only [sub_zero] using ha)
  have hcost : _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt (n+1-m+1:ℕ)*Real.sqrt (1-‖_root_.DerivativeChainContinuation.rootCentroid p‖^2) := by
    simpa only [one_pow,sub_zero] using hzc
  refine ⟨z,hzr,hz0,hcost.trans ?_⟩
  by_cases hV : 0 ≤ 1-‖_root_.DerivativeChainContinuation.rootCentroid p‖^2
  · have hs : (Real.sqrt (n+1-m+1:ℕ)*Real.sqrt (1-‖_root_.DerivativeChainContinuation.rootCentroid p‖^2))^2 ≤ (4:ℝ)^2 := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt hV]
      norm_num
      simpa only [Nat.cast_add,Nat.cast_one] using hbudget
    exact (sq_le_sq₀ (by positivity) (by norm_num)).mp hs
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hV),mul_zero]
    norm_num
