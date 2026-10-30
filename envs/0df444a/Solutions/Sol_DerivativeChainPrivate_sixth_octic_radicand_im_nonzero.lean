-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_radicand_im_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:23:59.527886+00:00
-- url     : https://prove2.me/submissions/0fdf9256-bcd7-4f63-9c6e-82d0bbfd5d0b

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (u : ℂ) (hu : ‖u‖≤3/10) (hi : u.im≠0) :
    (sixthOcticRadicand u).im≠0 := by
  let x:=u.re
  let Y:=u.im^2
  let V:=(3/10:ℝ)^2-x^2
  have hx : |x|≤3/10 := (Complex.abs_re_le_norm u).trans hu
  have hxlo : -(3/10:ℝ)≤x := (abs_le.mp hx).1
  have hxhi : x≤3/10 := (abs_le.mp hx).2
  have hy : 0≤Y := sq_nonneg _
  have hyV : Y≤V := by
    have hn:=Complex.sq_norm u
    simp only [Complex.normSq_apply] at hn
    dsimp [Y,V,x]
    nlinarith [norm_nonneg u]
  have hV : 0≤V := hy.trans hyV
  have hxsq : x^2≤(3/10:ℝ)^2 := by dsimp [V] at hV; linarith
  let A:=-(2210/363:ℝ)+(2*27455/2178)*x-(3*859775/84942)*x^2+
    (4*2088025/1019304)*x^3+(5*35496425/33637032)*x^4
  let B:=(859775/84942:ℝ)-(4*2088025/1019304)*x-(10*35496425/33637032)*x^2
  have hB : 0≤B+(35496425/33637032)*(Y+V) := by
    dsimp [B]
    nlinarith
  have hd:=mul_nonneg (sub_nonneg.mpr hyV) hB
  have hc : A+B*V+(35496425/33637032)*V^2<0 := by
    have ha : 0≤x+3/10 := by linarith
    have hb : 0≤3/10-x := by linarith
    have he : -(A+B*V+(35496425/33637032)*V^2)=
        1/2+(66704838875/538192512)*(3/10-x)^4+
          (34281639875/134548128)*(x+3/10)*(3/10-x)^3+
          (40900775225/269096256)*(x+3/10)^2*(3/10-x)^2+
          (1876437625/44849376)*(x+3/10)^3*(3/10-x)+
          (683445625/179397504)*(x+3/10)^4 := by
      dsimp [A,B,V]
      ring
    have hp : 0 < -(A+B*V+(35496425/33637032)*V^2) := by rw [he]; positivity
    linarith
  have hneg : A+B*Y+(35496425/33637032)*Y^2<0 := by nlinarith
  have he : (sixthOcticRadicand u).im=u.im*(A+B*Y+(35496425/33637032)*Y^2) := by
    dsimp [sixthOcticRadicand,A,B,Y,x]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  exact mul_ne_zero hi (ne_of_lt hneg)
