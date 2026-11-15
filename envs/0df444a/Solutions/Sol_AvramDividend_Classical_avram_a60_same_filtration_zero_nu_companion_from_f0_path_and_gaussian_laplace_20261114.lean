-- Prove2me | solution 1 for AvramDividend.Classical.avram_a60_same_filtration_zero_nu_companion_from_f0_path_and_gaussian_laplace_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:32:52.075065+00:00
-- url     : https://prove2.me/submissions/c86186d3-aad8-4ecf-b6de-f38c1bcaa115

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a59_allpath_raw_gaussian_patch_retains_independent_stationary_increments_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ) (σ : ℝ)
    (hP : IsProbabilityMeasure P) (hσ : 0 ≤ σ)
    (hAdapt : ∀ t, Measurable[𝓕 t] (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (E : Set Ω)
    (hE : MeasurableSet[𝓕 0] E)
    (hAE : ∀ᵐ ω ∂P, ω ∈ E)
    (hGood : ∀ ω ∈ E, Continuous (fun t : ℝ≥0 => G t ω))
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P)
    (hStat : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P)
    (hLap : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) * (σ ^ 2 * θ ^ 2 / 2))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = σ ∧
      (∀ᵐ ω ∂P, ∀ t, Y.X t ω = G t ω) := by
  obtain ⟨H, hAdaptH, hZeroH, hEq, hCont, hIndH, hStatH⟩ :=
    avram_a59_allpath_raw_gaussian_patch_retains_independent_stationary_increments_20261114
      G hAdapt hZero E hE hAE hGood hInd hStat
  have hReg (ω : Ω) :=
    avram_a51_continuous_real_path_has_allpath_cadlag_no_positive_jumps_20261114
      (fun t => H t ω) (hCont ω)
  have hLapH (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
      Integrable (fun ω => Real.exp (θ * H t ω)) P ∧
      (∫ ω, Real.exp (θ * H t ω) ∂P) =
        Real.exp ((t : ℝ) * (σ ^ 2 * θ ^ 2 / 2)) := by
    obtain ⟨hIntG, hExpG⟩ := hLap t θ hθ
    have hAEexp : (fun ω => Real.exp (θ * H t ω)) =ᵐ[P]
        (fun ω => Real.exp (θ * G t ω)) := by
      filter_upwards [hEq] with ω hω
      rw [hω t]
    exact ⟨hIntG.congr hAEexp.symm,
      (integral_congr_ae hAEexp).trans hExpG⟩
  obtain ⟨Y, hYX, _, hYnu, hYσ⟩ :=
    avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
      H σ hP hσ hZeroH
      (fun ω t => (hReg ω).1 t)
      (fun ω t ht => (hReg ω).2.1 t ht)
      (fun ω t l ht hl => (hReg ω).2.2 t l ht hl)
      hAdaptH hIndH hStatH hLapH
  refine ⟨Y, hYnu, hYσ, ?_⟩
  filter_upwards [hEq] with ω hω
  intro t
  rw [hYX]
  exact hω t
