-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finiteactivity_original_continuous_gaussian_any_bounded_stop_initial_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:04:56.28951+00:00
-- url     : https://prove2.me/submissions/27836177-d70e-4e76-b5dd-9a9fe403eac5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical Gaussian residual has an original-space continuous martingale
version that is L1 and initially conditionally centred at any bounded stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (G t ω))) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      P[(fun ω => G (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
  obtain ⟨R, hR⟩ :=
    avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
      X hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) :=
    hR.mono (fun ω hω => hω.1)
  obtain ⟨G, hAdapt, _hZero, hSame, hCont, _hIndep,
      _hStat, hGcenter, hGmart⟩ :=
    avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
      X hX hFinite R hRsource
  have hGsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (G t ω)) := by
    filter_upwards [hRsource, hSame] with ω hlim hEq
    intro t
    simpa only [hEq t] using hlim t
  obtain ⟨hStopI, hStopCE⟩ :=
    avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
      X hX hFinite G hGsource (fun t => (hGcenter t).1)
      hGmart n hn τ hτstop hτbound
  exact ⟨G, hAdapt, hCont, hGsource, hGcenter, hStopI, hStopCE⟩

