-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_real_product_L2_square_to_eNorm_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:23:10.75128+00:00
-- url     : https://prove2.me/submissions/8a985704-6893-4444-8ea0-01d27eb678db

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (hSquare : (∫⁻ a, ENNReal.ofReal ((f a) ^ 2) ∂μ) < ⊤) :
    (∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
  have heq : (fun a : α => ‖f a‖ₑ ^ (2 : ℝ)) =
      (fun a : α => ENNReal.ofReal ((f a) ^ 2)) := by
    funext a
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (f a)) 2, sq_abs]
  simpa only [heq] using hSquare
