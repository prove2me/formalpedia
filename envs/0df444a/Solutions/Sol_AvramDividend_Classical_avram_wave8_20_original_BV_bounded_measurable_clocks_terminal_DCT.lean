-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:52:37.917697+00:00
-- url     : https://prove2.me/submissions/dbf73b53-5bd1-4136-8316-c0e9537a525e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Genuine DCT interface for exact source BV killed terminals at measurable clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hτMeas : ∀ n, Measurable (τ n))
    (hτBound : ∀ n ω, τ n ω ≤ H)
    (f : Ω → ℝ)
    (hConv : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
          w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
      else 0) atTop (𝓝 (f ω))) :
    Tendsto (fun n : ℕ => ∫ ω,
      (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
          w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
      else 0) ∂P) atTop
      (𝓝 (∫ ω, f ω ∂P)) := by
  classical
  haveI : IsProbabilityMeasure P := X.isProbability
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  let Term : ℕ → Ω → ℝ := fun n ω =>
    if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
          w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
      else 0
  have hTermMeas : ∀ n, AEStronglyMeasurable (Term n) P := by
    intro n
    have hp : Measurable (fun ω => (τ n ω, ω)) :=
      (hτMeas n).prodMk measurable_id
    exact ((avram_wave8_20_original_strict_survival_terminal_joint_measurable
      X x D hStrat w hw_cont hw_neg q).comp hp).aestronglyMeasurable
  obtain ⟨K, hK0, hK⟩ :=
    avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
      X hX hBV q hq w hw_cont x C D hD H
  have hTermBound : ∀ n, ∀ᵐ ω ∂P, ‖Term n ω‖ ≤ K := by
    intro n
    filter_upwards [hK] with ω hKω
    have hNonneg : 0 ≤ Term n ω := by
      dsimp [Term]
      by_cases hs : (τ n ω : ℝ≥0∞) < ruinTime X x D ω
      · simpa only [if_pos hs] using
          (le_max_left (0 : ℝ)
            (Real.exp (-(q * (τ n ω : ℝ))) *
              w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω)))
      · simp only [if_neg hs, le_refl]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg] using
      hKω (τ n ω) (hτBound n ω)
  change Tendsto (fun n => ∫ ω, Term n ω ∂P) atTop
    (𝓝 (∫ ω, f ω ∂P))
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => K) hTermMeas (integrable_const K)
    hTermBound hConv
