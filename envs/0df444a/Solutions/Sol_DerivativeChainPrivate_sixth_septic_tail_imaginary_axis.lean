-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_tail_imaginary_axis
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:00:33.561638+00:00
-- url     : https://prove2.me/submissions/1bd53719-5356-41f8-bf6b-21288e9fea2c

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_radicand_positive
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

theorem sixth_septic_radicand_real (x : ℝ) : sixthSepticRadicand (x:ℂ) =
    ((1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4:ℝ):ℂ) := by
  simp [sixthSepticRadicand]
theorem sixth_septic_poly_real (x : ℝ) : sixthSepticPoly (x:ℂ) =
    ((1+x*(∑ i : Fin 20, sixthSepticCoeffs i*x^i.val):ℝ):ℂ) := by
  simp [sixthSepticPoly]
theorem sixth_septic_residual_real (x : ℝ) : sixthSepticResidual (x:ℂ) =
    ((∑ i : Fin 20, sixthSepticResidualCoeffs i*x^i.val : ℝ):ℂ) := by
  simp [sixthSepticResidual]
theorem sixth_septic_sqrt_real (x : ℝ) (hx : |x| ≤ 3/8) : Complex.sqrt (sixthSepticRadicand (x:ℂ)) =
    ((Real.sqrt (1-(2618/699)*x+(2890/699)*x^2-(122825/81783)*x^3+(417605/981396)*x^4):ℝ):ℂ) := by
  have hp := sixth_septic_radicand_positive (x:ℂ) (by simpa using hx)
  rw [sixth_septic_radicand_real,Complex.ofReal_re] at hp
  rw [sixth_septic_radicand_real,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),Complex.ofReal_re]






end DerivativeChainPrivate

theorem solution (x : ℝ) (hx : x^2 ≤ 2/7) : (sixthSepticTail (Complex.I*(x:ℂ))).re = 0 := by
  unfold sixthSepticTail
  rw [show (Complex.I*(x:ℂ))^2 = ((-x^2:ℝ):ℂ) by norm_num [mul_pow]]
  rw [sixth_septic_sqrt_real _ (by rw [abs_neg,abs_of_nonneg (sq_nonneg x)]; linarith),sixth_septic_poly_real,sixth_septic_residual_real]
  have he : (Complex.I*(x:ℂ))^39 = -Complex.I*((x^39:ℝ):ℂ) := by
    norm_num [mul_pow,Complex.I_pow_eq_pow_mod]
    norm_num [Complex.I_pow_three]
  rw [he]
  simp only [← Complex.ofReal_one,← Complex.ofReal_mul,← Complex.ofReal_sub,
    ← Complex.ofReal_add,← Complex.ofReal_neg,← Complex.ofReal_div]
  simp only [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,
    mul_one,one_mul,neg_zero,zero_div]
