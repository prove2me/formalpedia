-- Prove2me | solution 1 for CubicTurning.chain_start_middle
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:36:43.36813+00:00
-- url     : https://prove2.me/submissions/8d556efa-85b9-489a-9237-6f5182ac628d

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


theorem solution (a b c : ℂ) (hcenter : a+b+c=0)
    (hsecond : a^2+b^2+c^2=6) (z : Fin 3 → ℂ)
    (hz : DerivativeChainPrivate.IsChain ![a,b,c] z) :
    z 0=0 ∧ (z 1=1 ∨ z 1=-1) := by
  have hpair : a*b+a*c+b*c = -3 := by
    have hh : (a+b+c)^2=0 := by rw [hcenter]; norm_num
    linear_combination (hh-hsecond)/2
  have h₀:=hz 0
  have h₁:=hz 1
  simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,
    Fin.prod_univ_succ,Function.iterate_succ_apply,Polynomial.derivative_mul] at h₀ h₁
  refine ⟨?_,?_⟩
  · linear_combination (h₀+2*hcenter)/6
  · have hs : (z 1)^2=1 := by linear_combination (h₁+2*(z 1)*hcenter-hpair)/3
    have hp : (z 1-1)*(z 1+1)=0 := by linear_combination hs
    rcases mul_eq_zero.mp hp with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
