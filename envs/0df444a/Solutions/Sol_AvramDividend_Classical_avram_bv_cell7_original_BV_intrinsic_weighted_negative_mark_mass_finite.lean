-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:02:39.830234+00:00
-- url     : https://prove2.me/submissions/0b32b875-8c01-4e53-a4da-8b34fb2baa4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every nonnegative compact C1 envelope constant preserves the finite
    negative-mark intrinsic mass of the actual original BV Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (C : ℝ), 0 ≤ C →
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      (∫⁻ p, ENNReal.ofReal (C * (-p.2)) ∂NT) < ⊤ := by
  filter_upwards
    [AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_mass_finite_on_clock
      X hBV] with ω hω
  intro T C hC
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
        (fun u : ℝ≥0 => (u, Δ u)))
  have hfinite : (∫⁻ p, ENNReal.ofReal (-p.2) ∂NT) < ⊤ := hω T
  have hmeas : Measurable (fun p : ℝ≥0 × ℝ => ENNReal.ofReal (-p.2)) :=
    (measurable_snd.neg).ennreal_ofReal
  have hf : (∫⁻ p, ENNReal.ofReal (C * (-p.2)) ∂NT) =
      ENNReal.ofReal C * ∫⁻ p, ENNReal.ofReal (-p.2) ∂NT := by
    simp_rw [ENNReal.ofReal_mul hC]
    exact MeasureTheory.lintegral_const_mul (ENNReal.ofReal C) hmeas
  change (∫⁻ p, ENNReal.ofReal (C * (-p.2)) ∂NT) < ⊤
  rw [hf]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
