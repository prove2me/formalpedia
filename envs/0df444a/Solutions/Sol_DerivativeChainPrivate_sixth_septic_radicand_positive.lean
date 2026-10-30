-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_radicand_positive
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:58:21.817916+00:00
-- url     : https://prove2.me/submissions/6e659d20-e60b-49b4-8c4c-46e38876d456

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
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


theorem solution (u : ℂ) (hu : ‖u‖≤3/8) :
    0<(sixthSepticRadicand u).re := by
  let x:=u.re
  let Y:=u.im^2
  let V:=(3/8:ℝ)^2-x^2
  have hx : |x|≤3/8 := (Complex.abs_re_le_norm u).trans hu
  have hxlo : -(3/8:ℝ)≤x := (abs_le.mp hx).1
  have hxhi : x≤3/8 := (abs_le.mp hx).2
  have hy : 0≤Y := sq_nonneg _
  have hyV : Y≤V := by
    have hn:=Complex.sq_norm u
    simp only [Complex.normSq_apply] at hn
    dsimp [Y,V,x]
    nlinarith [norm_nonneg u]
  let B:=-(2890/699:ℝ)+(368475/81783)*x-(2505630/981396)*x^2
  have hB : B+(417605/981396)*(Y+V)≤0 := by
    dsimp [B,V] at *
    nlinarith [sq_nonneg x]
  have hd:=mul_nonneg (sub_nonneg.mpr hyV) (neg_nonneg.mpr hB)
  have he : (sixthSepticRadicand u).re=
      1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4+
        B*Y+(417605/981396)*Y^2 := by
    dsimp [sixthSepticRadicand,x,Y,B]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hbase :
      0<1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4+
        B*V+(417605/981396)*V^2 := by
    have hxr : 0≤3/8-x := sub_nonneg.mpr hxhi
    have hid :
        1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4+
          B*V+(417605/981396)*V^2 =
        (835210/245349)*(x-1/4)^4+
          (49130/18873)*(3/8-x)*(x-1/4)^2+
          (33256675/7851168)*(x-1/4-30079/1956275)^2+
          25157258143583/462578256691200 := by
      dsimp [B,V]
      ring
    rw [hid]
    positivity
  rw [he]
  nlinarith
