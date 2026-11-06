-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_real_mapped_finite_horizon_gaussian_small_joint_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:41:09.424618+00:00
-- url     : https://prove2.me/submissions/5887b386-0f72-44a2-831b-10e715a4b636

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original real-time finite horizon mapped to nonnegative time carries physical joint energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (T : ℝ≥0) :
    let μtime : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let μ : Measure (ℝ≥0 × Ω) := μtime.prod P
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
    (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U p + z) - w (U p)) -
          (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  have htime : (volume : Measure ℝ) (Icc (0 : ℝ) (T : ℝ)) ≠ ⊤ := by
    exact (measure_Icc_lt_top).ne
  haveI hrestricted : IsFiniteMeasure
      ((volume : Measure ℝ).restrict (Icc (0 : ℝ) (T : ℝ))) :=
    (isFiniteMeasure_restrict).2 htime
  haveI hmapped : IsFiniteMeasure
      (((volume : Measure ℝ).restrict (Icc (0 : ℝ) (T : ℝ))).map Real.toNNReal) :=
    Measure.isFiniteMeasure_map _ Real.toNNReal
  exact
    avram_p4_f3_original_finite_time_product_gaussian_small_joint_energy
      X x D w C hw_cont hw_neg hw_smooth δ K ε hδ hδK hK _
