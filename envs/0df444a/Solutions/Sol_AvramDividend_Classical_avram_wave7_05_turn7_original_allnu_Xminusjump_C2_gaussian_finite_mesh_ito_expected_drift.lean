-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_C2_gaussian_finite_mesh_ito_expected_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:11:57.724585+00:00
-- url     : https://prove2.me/submissions/537b5684-8bdc-4968-adce-87851bf8c930

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

/-! Exact original X minus small and large jump parts gives finite C2 stopped Ito Gaussian half sigma squared expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
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
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    Integrable (fun ω => ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2) ∂P) =
      ∑ i ∈ S, ((((h i : ℝ) * X.σ ^ 2) / 2) *
        (∫ ω, H i ω ∂P)) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ι → Ω → ℝ := fun i ω =>
    M (τ i ω + h i) ω - M (τ i ω) ω
  let W : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
      (h i : ℝ) * Y.c
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hV : V = W := by
    funext i ω
    dsimp [V, W]
    rw [hM (τ i ω + h i) ω, hM (τ i ω) ω]
    push_cast
    ring
  have hCells :=
    avram_wave7_05_turn7_original_allnu_source_C2_gaussian_finite_mesh_ito_expected_drift
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T S τ hτ B hbounded h G H hGsource hHsource
      BG BH hBG hBH hGbound hHbound
  dsimp only at hCells
  change Integrable (fun ω => ∑ i ∈ S,
    (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2) ∂P) =
      ∑ i ∈ S, ((((h i : ℝ) * X.σ ^ 2) / 2) *
        (∫ ω, H i ω ∂P))
  rw [hV]
  exact hCells
