-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_finite_stopped_cash_real_prefix_plus_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:27:20.412311+00:00
-- url     : https://prove2.me/submissions/dc9739da-ec72-4b97-ac5e-e60192af63d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ) (hab : a ≤ b)
    (hFin :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic a,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  let A : ℝ≥0∞ :=
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic a,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  let B : ℝ≥0∞ :=
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  let Ccash : ℝ≥0∞ :=
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  have hsplit : Ccash = A + B :=
    avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
      X x q D ω a b hab
  have hA : A < ⊤ := by
    have hle : A ≤ Ccash := by
      rw [hsplit]
      exact le_add_right (le_refl A)
    exact lt_of_le_of_lt hle hFin
  have hB : B < ⊤ := by
    have hle : B ≤ Ccash := by
      rw [hsplit]
      exact le_add_left (le_refl B)
    exact lt_of_le_of_lt hle hFin
  change Ccash.toReal = A.toReal + B.toReal
  rw [hsplit]
  exact ENNReal.toReal_add hA.ne hB.ne
