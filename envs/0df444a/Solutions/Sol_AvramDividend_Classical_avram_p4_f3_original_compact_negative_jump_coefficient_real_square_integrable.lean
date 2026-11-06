-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_coefficient_real_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:13:05.717652+00:00
-- url     : https://prove2.me/submissions/0f72835b-7b74-4588-99b0-d303a98760c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-jump stochastic coefficient has true real L2 energy with respect to its physical Levy measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∀ u ∈ Icc δ K,
      IntegrableOn (fun z : ℝ => (w (u + z) - w u) ^ 2)
        (Iio (0 : ℝ)) X.ν := by
  have hwMeas : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable
      w hw_cont hw_neg
  intro u hu
  have hLin :
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) < ⊤ :=
    avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
      X w C hw_cont hw_neg hw_smooth δ K hδ hδK hK u hu
  have hNonneg :
      0 ≤ᵐ[X.ν.restrict (Iio (0 : ℝ))]
        (fun z : ℝ => (w (u + z) - w u) ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hFin :
      HasFiniteIntegral (fun z : ℝ => (w (u + z) - w u) ^ 2)
        (X.ν.restrict (Iio (0 : ℝ))) :=
    (hasFiniteIntegral_iff_ofReal hNonneg).2 hLin
  have hMeas :
      Measurable (fun z : ℝ => (w (u + z) - w u) ^ 2) :=
    ((hwMeas.comp (measurable_const.add measurable_id)).sub
      measurable_const).pow_const 2
  change Integrable (fun z : ℝ => (w (u + z) - w u) ^ 2)
    (X.ν.restrict (Iio (0 : ℝ)))
  exact ⟨hMeas.aestronglyMeasurable, hFin⟩
