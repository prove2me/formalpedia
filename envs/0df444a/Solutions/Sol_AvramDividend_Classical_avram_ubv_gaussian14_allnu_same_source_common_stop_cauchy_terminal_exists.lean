-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian14_allnu_same_source_common_stop_cauchy_terminal_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:35:11.15557+00:00
-- url     : https://prove2.me/submissions/85cde67c-45dc-4ac1-b5c9-70fb441ee448

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_centred_L2_cauchy_limit_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original X-minus-jumps stopped Gaussian finite grids construct their
own centred terminal L² stochastic integral from pairwise L² Cauchyness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : ℕ → Finset ι) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ (n : ℕ) (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hB : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n i, i ∈ S n → G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * (M (τ n ω + h n i) ω - M (τ n ω) ω)
    Tendsto (fun nm : ℕ × ℕ => eLpNorm (Q nm.1 - Q nm.2) 2 P)
      atTop (𝓝 0) →
    ∃ L : Ω → ℝ, MemLp L 2 P ∧
      (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, G n i ω * (M (τ n ω + h n i) ω - M (τ n ω) ω)
  change Tendsto (fun nm : ℕ × ℕ => eLpNorm (Q nm.1 - Q nm.2) 2 P)
      atTop (𝓝 0) →
    ∃ L : Ω → ℝ, MemLp L 2 P ∧ (∫ ω, L ω ∂P) = 0 ∧
      Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0)
  intro hCauchy
  have hQ2 (n : ℕ) : MemLp (Q n) 2 P := by
    exact avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_L2
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T (τ n) (hτ n) (B n) (hB n)
      (S n) (h n) (G n) (hGsource n) (K n) (hK n) (hGbound n)
  have hQzero (n : ℕ) : (∫ ω, Q n ω ∂P) = 0 := by
    exact (avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T (S n) (fun _ : ι => τ n)
      (fun _ _ s => hτ n s) (fun _ : ι => B n)
      (fun _ _ ω => hB n ω) (h n) (G n) (hGsource n)
      (K n) (hK n) (hGbound n)).2
  exact avram_ubv_gaussian14_centred_L2_cauchy_limit_exists
    P Q hQ2 hQzero hCauchy
