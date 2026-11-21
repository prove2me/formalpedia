-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_finitecap_original_fullnegative_value_increment_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T18:27:41.217531+00:00
-- url     : https://prove2.me/submissions/f6f04bcb-d17e-4cc2-89ea-008df9f4c551

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (μ : Measure α) (hμ : μ Set.univ < ⊤)
    (Y : α → ℝ) (hY : ∀ a, 0 ≤ Y a ∧ ENNReal.ofReal (Y a) ≤ C)
    (G : α × ℝ → ℝ)
    (hG : ∀ p, G p = if p.2 < 0 then w (Y p.1 + p.2) - w (Y p.1) else 0)
    (hGmeas : AEStronglyMeasurable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  classical
  haveI : IsFiniteMeasure μ := ⟨hμ⟩
  have hνfinite : (X.ν.restrict (Iio (0 : ℝ))) Set.univ < ⊤ := by
    simpa using (lt_top_iff_ne_top.mpr hFinite)
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := ⟨hνfinite⟩
  obtain ⟨M, hM, hbound⟩ :=
    avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
      C hCfinite w hw_cont hw_neg
  refine Integrable.of_bound hGmeas (2 * M) ?_
  filter_upwards [] with p
  rcases p with ⟨a, z⟩
  rw [hG]
  by_cases hz : z < 0
  · rw [if_pos hz, Real.norm_eq_abs]
    exact hbound (Y a) z (hY a).1 (hY a).2 hz
  · rw [if_neg hz, norm_zero]
    nlinarith [hM]
