-- Prove2me | solution 1 for DerivativeChainContinuation.complex_tower_factor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:43:08.032293+00:00
-- url     : https://prove2.me/submissions/43dbe7b4-ad60-44aa-b14e-1d67e3d10e0e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n,UniformPolynomialStep r k) (k : ℕ) (hk : k≤n) :
    ∃ c : ℂ,c≠0 ∧ (derivative^[n-k] (complexRowProduct r n))=C c*complexRowProduct r k := by
  induction n with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    exact ⟨1,one_ne_zero,by simp⟩
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      exact ⟨1,one_ne_zero,by simp⟩
    obtain ⟨c,hc,heq⟩ := ih (fun j hj => hstep j (by omega)) (by omega)
    have hnC : (n+2:ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
    refine ⟨(n+2:ℂ)*c,mul_ne_zero hnC hc,?_⟩
    rw [show n+1-k=(n-k)+1 by omega,Function.iterate_succ_apply,(hstep n (by omega)).1,
      iterate_derivative_C_mul,heq,map_mul,mul_assoc]
