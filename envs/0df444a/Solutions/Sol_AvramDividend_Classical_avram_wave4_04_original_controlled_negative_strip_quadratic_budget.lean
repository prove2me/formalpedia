-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_original_controlled_negative_strip_quadratic_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:19:03.770663+00:00
-- url     : https://prove2.me/submissions/9858e862-8cf5-4118-809c-02bd36a05369

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- A single source-jump quadratic envelope controls every negative-mark truncation strip
for the actual controlled left-limit reserve and any predictable-space measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E : Set ℝ,
      MeasurableSet E → E ⊆ Iio (0 : ℝ) →
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
        μ Set.univ * (ENNReal.ofReal K *
          (∫⁻ z in E, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν)) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Iio (0 : ℝ) →
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
    μ Set.univ * (ENNReal.ofReal K *
      (∫⁻ z in E, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν))
  obtain ⟨K, hK, hpoint, _⟩ :=
    avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
      X w a b u v δ hw hw_cont hw_neg hau huv hvb hu0 hδ hδone hband
  refine ⟨K, hK, ?_⟩
  intro E hEm hEneg
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  have hpoint' (p : ℝ≥0 × Ω) (z : ℝ) (hz : z ∈ E) :
      ENNReal.ofReal ((H (p, z)) ^ 2) ≤
      ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) := by
    by_cases hb : Y p ∈ Icc (u + δ) v
    · simp only [H, if_pos hb]
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (hpoint (Y p) hb z (hEneg hz))
    · simp only [H, if_neg hb, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        ENNReal.ofReal_zero]
      exact bot_le
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν) ≤
        ENNReal.ofReal K *
          (∫⁻ z in E, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
    calc
      (∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν) ≤
          ∫⁻ z in E, ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              exact hpoint' p z hz
      _ = _ := lintegral_const_mul _ hνmeas
  calc
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in E, ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
        ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal K *
          (∫⁻ z in E, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) ∂μ :=
      lintegral_mono hinner
    _ = _ := by simp [mul_comm]
