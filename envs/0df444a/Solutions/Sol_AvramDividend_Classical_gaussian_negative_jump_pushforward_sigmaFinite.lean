-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_negative_jump_pushforward_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:33:52.891981+00:00
-- url     : https://prove2.me/submissions/fb25f06e-64f7-4a39-a13f-036aeb06dc97

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_support
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_supported_levy_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The negative-jump Lévy measure becomes globally sigma-finite after
passing to positive jump magnitudes. -/
theorem solution
    (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    SigmaFinite (ν.map (fun y : ℝ => -y)) := by
  have hsupport :=
    AvramDividend.Classical.gaussian_negative_jump_pushforward_support ν hν
  have hpositive :=
    AvramDividend.Classical.gaussian_levy_square_integrable_neg_pushforward
      ν hlevy
  exact AvramDividend.Classical.gaussian_positive_supported_levy_sigmaFinite
    (ν.map (fun y : ℝ => -y)) hsupport hpositive
