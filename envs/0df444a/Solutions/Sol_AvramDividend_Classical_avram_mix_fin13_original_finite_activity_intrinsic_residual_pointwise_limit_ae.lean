-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_pointwise_limit_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:02:27.855739+00:00
-- url     : https://prove2.me/submissions/9c88ca78-5ec8-499b-92da-84a371a73cc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∃ y : ℝ, Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (nhds y) := by
  filter_upwards
      [avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
        X hFinite] with ω hω
  intro t
  have hCauchy :
      CauchySeq (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hω t ε hε
    refine ⟨N, ?_⟩
    intro i hi j hj
    rcases le_total i j with hij | hji
    · have h := hN i j hi hij t le_rfl
      simpa only [Real.dist_eq, abs_sub_comm] using h
    · have h := hN j i hj hji t le_rfl
      simpa only [Real.dist_eq] using h
  exact cauchySeq_tendsto_of_complete hCauchy
