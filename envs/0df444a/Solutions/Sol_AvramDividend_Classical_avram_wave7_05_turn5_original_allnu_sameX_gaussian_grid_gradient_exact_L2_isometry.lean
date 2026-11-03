-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_exact_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:54:26.336125+00:00
-- url     : https://prove2.me/submissions/87d0dceb-5275-4644-aa23-eac7d8b1379c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-!
Original all-ν controlled Gaussian-residual finite-grid L² isometry.
The source gradient depends on X and D; Y is a pathwise component of X.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
        (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun _ => (s i : WithTop ℝ≥0)))
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S,
      MemLp (fun ω => G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (Y.X (t i) ω - Y.X (s i) ω -
      ((t i - s i) : ℝ) * Y.c)
  have hGrid :=
    avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
      Y hYν S s t G hst hSep hGown hGpair hLp
  dsimp only at hGrid
  exact hGrid
