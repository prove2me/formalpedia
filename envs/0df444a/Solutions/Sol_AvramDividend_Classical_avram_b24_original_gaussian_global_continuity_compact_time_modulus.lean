-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_gaussian_global_continuity_compact_time_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:01:43.282314+00:00
-- url     : https://prove2.me/submissions/11515dc5-e05a-4404-81c8-b84df666bc1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε := by
  have hCont :=
    avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
      X hFinite R hRsource
  filter_upwards [hCont] with ω hω ε hε
  have hUC : UniformContinuousOn (fun t : ℝ≥0 => R t ω) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hω.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff_le.mp hUC) ε hε
  let δNN : ℝ≥0 := ⟨δ, le_of_lt hδ⟩
  refine ⟨δNN, ?_, ?_⟩
  · exact_mod_cast hδ
  · intro s t hst ht hgap
    have hs : s ∈ Icc (0 : ℝ≥0) T :=
      ⟨(show (0 : ℝ≥0) ≤ s from zero_le), le_trans hst ht⟩
    have htt : t ∈ Icc (0 : ℝ≥0) T := ⟨(show (0 : ℝ≥0) ≤ t from zero_le), ht⟩
    have hd : dist s t ≤ δ := by
      rw [NNReal.dist_eq]
      have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hstR)]
      have hco : ((t - s : ℝ≥0) : ℝ) ≤ δ := by
        exact_mod_cast hgap
      simpa only [NNReal.coe_sub hst] using hco
    have hRes := hmod s hs t htt hd
    simpa only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hRes
