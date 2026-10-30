-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_tail_imaginary_axis
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:16:53.217014+00:00
-- url     : https://prove2.me/submissions/2cac525e-112d-4f45-82e2-c5a3d1f31904

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_real_positive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem sixth_octic_radicand_real (x : ℝ) : sixthOcticRadicand (x:ℂ)=
    ((1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
      (2088025/1019304)*x^4+(35496425/33637032)*x^5:ℝ):ℂ) := by
  simp [sixthOcticRadicand]
theorem sixth_octic_poly_real (x : ℝ) : sixthOcticPoly (x:ℂ)=
    ((1+x*(∑ i : Fin 20,sixthOcticCoeffs i*x^i.val):ℝ):ℂ) := by simp [sixthOcticPoly]
theorem sixth_octic_residual_real (x : ℝ) : sixthOcticResidual (x:ℂ)=
    ((∑ i : Fin 20,sixthOcticResidualCoeffs i*x^i.val:ℝ):ℂ) := by simp [sixthOcticResidual]
theorem sixth_octic_sqrt_real (x : ℝ) (hx : |x|≤3/10) :
    Complex.sqrt (sixthOcticRadicand (x:ℂ))=
      ((Real.sqrt (1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
        (2088025/1019304)*x^4+(35496425/33637032)*x^5):ℝ):ℂ) := by
  have hp:=sixth_octic_real_positive x hx
  rw [sixth_octic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]






end DerivativeChainPrivate

theorem solution (x : ℝ) (hx : x^2≤1/4) :
    (sixthOcticTail (Complex.I*(x:ℂ))).re=0 := by
  unfold sixthOcticTail
  rw [show (Complex.I*(x:ℂ))^2=((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [sixth_octic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),sixth_octic_poly_real,sixth_octic_residual_real]
  have he : (Complex.I*(x:ℂ))^39=-Complex.I*((x^39:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod] <;> norm_num [Complex.I_pow_three]
  rw [he]
  rw [show (17/33:ℂ)=((17/33:ℝ):ℂ) by norm_num]
  simp only [←Complex.ofReal_one,←Complex.ofReal_mul,←Complex.ofReal_sub,
    ←Complex.ofReal_add,←Complex.ofReal_neg,←Complex.ofReal_div,←Complex.ofReal_pow]
  simp only [Complex.sub_re,Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,zero_sub,mul_one,one_mul,neg_zero,zero_div]
