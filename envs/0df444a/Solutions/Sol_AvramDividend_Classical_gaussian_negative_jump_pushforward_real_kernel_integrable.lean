-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_negative_jump_pushforward_real_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:31:36.746773+00:00
-- url     : https://prove2.me/submissions/57db982b-9c25-43e5-9b4d-f23f04943bac

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (ν : Measure ℝ) (hν : ν (Ici (0 : ℝ)) = 0)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (φ : ℝ) (hφ : 0 < φ) :
    IntegrableOn (fun t : ℝ => (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0)
          ∂(ν.map (fun y : ℝ => -y))).toReal) (Ioi (0 : ℝ)) volume := by
  letI : SigmaFinite (ν.map (fun y : ℝ => -y)) :=
    gaussian_negative_jump_pushforward_sigmaFinite ν hν hlevy
  have hpositive :=
    gaussian_levy_square_integrable_neg_pushforward ν hlevy
  exact (gaussian_double_tail_real_kernel_integrable
    (ν.map (fun y : ℝ => -y)) φ hφ hpositive).integrableOn
