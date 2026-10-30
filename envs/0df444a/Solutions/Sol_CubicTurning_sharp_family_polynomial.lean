-- Prove2me | solution 1 for CubicTurning.sharp_family_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:54:11.88462+00:00
-- url     : https://prove2.me/submissions/373e662b-907a-4354-9893-34a0dc4192be

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning












theorem sharp_family_center (t : ℝ) :
    sharpCentral t+sharpOuterPlus t+sharpOuterMinus t=0 := by
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

theorem sharp_family_second (t : ℝ) :
    (sharpCentral t)^2+(sharpOuterPlus t)^2+(sharpOuterMinus t)^2=6 := by
  have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  simp only [pow_two] at hs
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
    Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]


















































end CubicTurning

open CubicTurning in
theorem solution (t : ℝ) :
    DerivativeChainPrivate.fromRoots (![sharpCentral t,sharpOuterPlus t,sharpOuterMinus t] : Fin 3 → ℂ)=
      Polynomial.X^3-Polynomial.C 3*Polynomial.X+
        Polynomial.C (Complex.I*(t:ℂ)*(3+(t:ℂ)^2)) := by
  let a:=sharpCentral t
  let b:=sharpOuterPlus t
  let c:=sharpOuterMinus t
  have hcenter : a+b+c=0 := sharp_family_center t
  have hsecond : a^2+b^2+c^2=6 := sharp_family_second t
  have hpair : a*b+a*c+b*c = -3 := by
    have hh : (a+b+c)^2=0 := by rw [hcenter]; norm_num
    linear_combination (hh-hsecond)/2
  have hprod : a*b*c = -Complex.I*(t:ℂ)*(3+(t:ℂ)^2) := by
    have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
    simp only [pow_two] at hs
    have hst := congrArg (fun x : ℝ => t*x) hs
    apply Complex.ext <;> simp [a,b,c,sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
      Complex.mul_re,Complex.mul_im] <;> nlinarith [hs,hst]
  have he : (Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b)*(Polynomial.X-Polynomial.C c)=
      Polynomial.X^3-Polynomial.C (a+b+c)*Polynomial.X^2+
        Polynomial.C (a*b+a*c+b*c)*Polynomial.X-Polynomial.C (a*b*c) := by
    simp only [map_add,map_mul]
    ring
  unfold DerivativeChainPrivate.fromRoots
  simp only [Fin.prod_univ_succ]
  change (Polynomial.X-Polynomial.C a)*((Polynomial.X-Polynomial.C b)*
    ((Polynomial.X-Polynomial.C c)*1))=_
  rw [←mul_assoc, mul_one,he,hcenter,hpair,hprod]
  simp
  ring
