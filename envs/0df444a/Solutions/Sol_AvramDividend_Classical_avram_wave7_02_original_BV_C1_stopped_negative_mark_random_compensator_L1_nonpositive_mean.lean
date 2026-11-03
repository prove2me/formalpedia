-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:25:14.765205+00:00
-- url     : https://prove2.me/submissions/8f7d025d-8470-48bd-ba86-cd319ba4b166

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The actual C1 candidate at the original predictable left reserve gives
an L1 negative physical-time Levy compensator, including ruin-crossing marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (E : Set (ℝ≥0 × Ω))
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  have hGNeg : ∀ p, G p ≤ 0 := by
    intro p
    rw [hG p]
    split_ifs with hp
    · obtain ⟨hE, hz⟩ := hp
      have hDrop :=
        avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
          X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
          x D p.1.2 p.1.1 (hEregion p.1 hE) p.2 (le_of_lt hz)
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr hDrop)
    · exact le_refl 0
  obtain ⟨μ, hμfinite, hμclock, hPathInt, hMean⟩ :=
    avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
      X T G hGMeas hGNeg hGInt
  exact ⟨hPathInt, hMean⟩
