-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_finite_mesh_expected_half_sigma_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:33:04.060215+00:00
-- url     : https://prove2.me/submissions/e24c0bfa-9704-4b0e-8300-391c49bd7dc2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_source_C2_gaussian_finite_mesh_ito_expected_drift
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Direct original X zero-jump finite stopped C2 Ito expected Gaussian sigma squared half-drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BG BH : ι → ℝ)
    (hBG : ∀ i ∈ S, 0 ≤ BG i) (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ BG i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let V : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c
    Integrable (fun ω => ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2) ∂P) =
      ∑ i ∈ S, ((((h i : ℝ) * X.σ ^ 2) / 2) *
        (∫ ω, H i ω ∂P)) := by
  classical
  have hSource : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) + (0 : ℝ) + (0 : ℝ) := by
    intro t ω
    ring
  have hOne :=
    avram_wave7_05_turn7_original_allnu_source_C2_gaussian_finite_mesh_ito_expected_drift
      X X hν rfl (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      hSource x D hD w C hw q T S τ hτ B hbounded
      h G H hGsource hHsource BG BH hBG hBH hGbound hHbound
  dsimp only at hOne
  simpa only [sub_zero] using hOne
