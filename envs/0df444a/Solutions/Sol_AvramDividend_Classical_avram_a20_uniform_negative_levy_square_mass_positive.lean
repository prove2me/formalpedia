-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_uniform_negative_levy_square_mass_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:42:28.813899+00:00
-- url     : https://prove2.me/submissions/b70eaac3-170f-43e2-9940-1f6852db817a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Nonzero quadratic energy on the actual uniform negative-unit Lévy mark measure. -/
theorem solution :
    0 < (∫ z in Ioo (-1 : ℝ) 0, z ^ 2
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) := by
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  let μ : Measure ℝ := ((volume : Measure ℝ).restrict S).restrict S
  let f : ℝ → ℝ := fun z => z ^ 2
  letI : IsFiniteMeasure μ := by dsimp [μ, S]; infer_instance
  have hFm : Measurable f := by fun_prop
  have hNonneg : 0 ≤ f := fun z => sq_nonneg z
  have hBound : ∀ᵐ z ∂μ, ‖f z‖ ≤ (1 : ℝ) := by
    have hmem : ∀ᵐ z ∂μ, z ∈ S := by
      dsimp [μ]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with z hz
    have hneg : (-1 : ℝ) < z := hz.1
    have hzero : z < 0 := hz.2
    change ‖z ^ 2‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    nlinarith
  have hFi : Integrable f μ :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 hBound
  have hS : (0 : ℝ≥0∞) < μ S := by
    dsimp [μ, S]
    norm_num [Measure.restrict_apply, Real.volume_Ioo]
  have hSub : S ⊆ Function.support f := by
    intro z hz
    change z ^ 2 ≠ 0
    exact pow_ne_zero _ (ne_of_lt hz.2)
  have hPos : (0 : ℝ) < ∫ z, f z ∂μ :=
    (integral_pos_iff_support_of_nonneg hNonneg hFi).2
      (lt_of_lt_of_le hS (measure_mono hSub))
  change 0 < ∫ z, f z ∂μ
  exact hPos
