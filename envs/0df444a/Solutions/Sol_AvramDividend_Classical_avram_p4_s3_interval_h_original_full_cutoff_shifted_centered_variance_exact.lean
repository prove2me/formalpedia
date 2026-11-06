-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:52:12.905289+00:00
-- url     : https://prove2.me/submissions/5d8d702d-0f82-4515-90dc-cc867abb9cf8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
    intro ω
    rfl
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  obtain ⟨h0Int, h0Eq⟩ :=
    avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact X T n
  have hg : Measurable (fun z : ℝ≥0∞ => (z.toReal - r) ^ 2) := by
    fun_prop
  have hShift :=
    avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
      X NX hNX s T B measurableSet_Iic
      (fun z : ℝ≥0∞ => (z.toReal - r) ^ 2) hg h0Int
  exact ⟨hShift.1, hShift.2.trans h0Eq⟩
