-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_two_marked_negative_cells_cross_product_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:12:51.677988+00:00
-- url     : https://prove2.me/submissions/04a915d0-72b5-4fe7-b2f1-df8157d9f14a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The product of two actual original marked jump cells is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (s₁ t₁ s₂ t₂ : ℝ≥0)
    (hst₁ : s₁ ≤ t₁) (htT₁ : t₁ ≤ T)
    (hst₂ : s₂ ≤ t₂) (htT₂ : t₂ ≤ T)
    (B₁ B₂ : Set ℝ)
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hSep₁ : B₁ ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (hSep₂ : B₂ ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    let N₁ : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s₁ t₁ ×ˢ B₁)
    let N₂ : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s₂ t₂ ×ˢ B₂)
    Integrable (fun ω => (N₁ ω).toReal * (N₂ ω).toReal) P := by
  let N₁ : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s₁ t₁ ×ˢ B₁)
  let N₂ : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s₂ t₂ ×ˢ B₂)
  change Integrable (fun ω => (N₁ ω).toReal * (N₂ ω).toReal) P
  have hL₂₁ : Integrable (fun ω => (N₁ ω).toReal ^ 2) P :=
    (avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
      X T n s₁ t₁ hst₁ htT₁ B₁ hB₁ hSep₁).1
  have hL₂₂ : Integrable (fun ω => (N₂ ω).toReal ^ 2) P :=
    (avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
      X T n s₂ t₂ hst₂ htT₂ B₂ hB₂ hSep₂).1
  have hNm₁ : Measurable N₁ :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s₁ t₁ ×ˢ B₁) (measurableSet_Ioc.prod hB₁)
  have hNm₂ : Measurable N₂ :=
    avram_p2_d_future_intrinsic_general_time_mark_measurable
      X (Ioc s₂ t₂ ×ˢ B₂) (measurableSet_Ioc.prod hB₂)
  have hMeas : Measurable (fun ω => (N₁ ω).toReal * (N₂ ω).toReal) :=
    (ENNReal.measurable_toReal.comp hNm₁).mul
      (ENNReal.measurable_toReal.comp hNm₂)
  have hMajorant :
      Integrable (fun ω => (N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2) P :=
    hL₂₁.add hL₂₂
  apply Integrable.mono hMajorant hMeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hLower :
      -((N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2) ≤
        (N₁ ω).toReal * (N₂ ω).toReal := by
    nlinarith [sq_nonneg ((N₁ ω).toReal + (N₂ ω).toReal)]
  have hUpper :
      (N₁ ω).toReal * (N₂ ω).toReal ≤
        (N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2 := by
    nlinarith [sq_nonneg ((N₁ ω).toReal - (N₂ ω).toReal)]
  have hAbs := abs_le.mpr ⟨hLower, hUpper⟩
  change ‖(N₁ ω).toReal * (N₂ ω).toReal‖ ≤
    ‖(N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2‖
  have hSumNonneg : 0 ≤ (N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    ‖(N₁ ω).toReal * (N₂ ω).toReal‖ =
        |(N₁ ω).toReal * (N₂ ω).toReal| := Real.norm_eq_abs _
    _ ≤ (N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2 := hAbs
    _ = ‖(N₁ ω).toReal ^ 2 + (N₂ ω).toReal ^ 2‖ :=
      (Real.norm_of_nonneg hSumNonneg).symm
