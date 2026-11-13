-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_terminal_positive_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:11:05.937789+00:00
-- url     : https://prove2.me/submissions/3bc76a8d-06df-4ab6-9d60-6ccc161d0733

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a41_original_terminal_cell_envelope_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    let F : ℕ → Ω → ℝ := fun m ω =>
      if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
    ∃ g : Ω → ℝ, Integrable g P ∧
      (∀ m : ℕ, AEStronglyMeasurable (F m) P) ∧
      (∀ m : ℕ, ∀ᵐ ω ∂P, ‖F m ω‖ ≤ g ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨theta, K, L, htheta, hK, hL, hFMeas, hBound⟩ :=
    avram_ga_a41_original_terminal_cell_envelope_package
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have hSigma : 0 < X.σ :=
    avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded X hNuZero hBV
  have hExpMoment : (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp
        (theta * runningSup X (n : ℝ≥0) ω)) ∂P) < ⊤ :=
    avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
      X hSigma (n : ℝ≥0) theta htheta
  have hPair : Measurable (fun ω : Ω => ((n : ℝ≥0), ω)) :=
    Measurable.prod measurable_const measurable_id
  have hSup : Measurable (fun ω : Ω =>
      runningSup X (n : ℝ≥0) ω) :=
    (levy_runningSup_joint_time_path_measurable X).comp hPair
  have hExpMeas : Measurable (fun ω : Ω =>
      Real.exp (theta * runningSup X (n : ℝ≥0) ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hSup)
  have hExpNonneg : 0 ≤ᵐ[P]
      (fun ω : Ω =>
        Real.exp (theta * runningSup X (n : ℝ≥0) ω)) :=
    Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))
  have hExpInt : Integrable (fun ω : Ω =>
      Real.exp (theta * runningSup X (n : ℝ≥0) ω)) P :=
    (lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable hExpNonneg).mp
        (ne_of_lt hExpMoment)
  have hG : Integrable (fun ω : Ω =>
      K * Real.exp (theta * runningSup X (n : ℝ≥0) ω) + L) P :=
    (hExpInt.const_mul K).add (integrable_const L)
  exact ⟨fun ω => K * Real.exp
    (theta * runningSup X (n : ℝ≥0) ω) + L,
    hG, hFMeas, hBound⟩
