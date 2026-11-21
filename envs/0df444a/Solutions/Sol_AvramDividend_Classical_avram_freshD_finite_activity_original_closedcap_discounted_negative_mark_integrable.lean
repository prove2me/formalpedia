-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:38:06.90867+00:00
-- url     : https://prove2.me/submissions/482dccc9-26f6-4da7-9443-8040db714c80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ⊤)
    (q : ℝ) (hq : 0 ≤ q) (Y : ℝ≥0 × Ω → ℝ)
    (σ : Ω → ℝ≥0) (τ : Ω → ℝ≥0∞)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p =
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0)
    (hHm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H) :
    Integrable H (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  haveI : IsFiniteMeasure μ := ⟨hμfinite⟩
  have hν : (X.ν.restrict (Iio (0 : ℝ))) Set.univ < ⊤ := by
    simpa using (lt_top_iff_ne_top.mpr hFinite)
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := ⟨hν⟩
  obtain ⟨M, hM, hb⟩ :=
    avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
      C hCfinite w hw_cont hw_neg
  have hnorm : ∀ p, ‖H p‖ ≤ 2 * M := by
    intro ⟨⟨t, ω⟩, z⟩
    rw [hH]
    by_cases hc : 0 < t ∧ t ≤ σ ω ∧ (t : ℝ≥0∞) ≤ τ ω ∧
        0 ≤ Y (t, ω) ∧ ENNReal.ofReal (Y (t, ω)) ≤ C ∧ z < 0
    · have hcond := hc
      rcases hc with ⟨ht, hs, hr, hy, hcap, hz⟩
      have hw := hb (Y (t, ω)) z hy hcap hz
      have he : |Real.exp (-(q * (t : ℝ)))| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by
          nlinarith [mul_nonneg hq (show (0 : ℝ) ≤ t from t.property)])
      rw [if_pos hcond, Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ (1 : ℝ) * (2 * M) :=
          mul_le_mul he hw (abs_nonneg _) (by linarith [hM])
        _ = 2 * M := by ring
    · rw [if_neg hc, norm_zero]
      linarith [hM]
  haveI : IsFiniteMeasure (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
    inferInstance
  exact Integrable.of_bound hHm.aestronglyMeasurable (2 * M)
    (Filter.Eventually.of_forall hnorm)
