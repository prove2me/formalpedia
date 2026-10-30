-- Prove2me | solution 1 for CubicTurning.actual_history_affine
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:21:33.775721+00:00
-- url     : https://prove2.me/submissions/7f4f96d3-fd1b-4962-ae2a-9f12e84c1995

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


open CubicTurning in
/-- Affine images of normal-form histories are chains of the affine root tuple. -/
theorem solution (r : ℝ) (a b c v u t : ℂ)
    (hcenter : a+b+c=0) (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2)
    (hv : v=a ∨ v=b ∨ v=c) :
    DerivativeChainPrivate.IsChain ![u+t*a,u+t*b,u+t*c]
      ![u,u+t*middle r v,u+t*v] := by
  have hpair : a*b+a*c+b*c = -3*(r:ℂ)^2 := by
    have hh : (a+b+c)^2=0 := by rw [hcenter]; norm_num
    linear_combination (hh-hsecond)/2
  intro i
  fin_cases i
  · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,
      Fin.prod_univ_succ,Function.iterate_succ_apply,Polynomial.derivative_mul]
    linear_combination -2*t*hcenter
  · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,
      Fin.prod_univ_succ,Polynomial.derivative_mul]
    unfold middle
    split_ifs
    · linear_combination (-2*t^2*(r:ℂ))*hcenter+t^2*hpair
    · linear_combination (2*t^2*(r:ℂ))*hcenter+t^2*hpair
  · rcases hv with rfl|rfl|rfl <;>
      simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ]
