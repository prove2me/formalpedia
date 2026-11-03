-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_auto_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:55:05.348879+00:00
-- url     : https://prove2.me/submissions/7c14f7ab-2ac5-4115-bb67-523690854849

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-!
The original arbitrary-jump source gradient is automatically predictable.
The same-space Gaussian residual grid then has an exact L² isometry.
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
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
       else 0) *
      (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P) :
    let G : ι → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  classical
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    if u ≤ T then
      (Real.exp (-(q * (u : ℝ))) *
        deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
      (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  let G : ι → Ω → ℝ := fun i ω => Z (s i) ω
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (Y.X (t i) ω - Y.X (s i) ω -
      ((t i - s i) : ℝ) * Y.c)
  have hPred : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T
  have hGown : ∀ i ∈ S,
      Measurable[𝓕.rightCont (s i)] (G i) := by
    intro i hi
    exact (hPred.stronglyAdapted (s i)).measurable
  have hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i) := by
    intro i hi j hj hij
    exact (hGown i hi).mono
      ((𝓕.rightCont).mono (le_trans (hst i hi) hij)) le_rfl
  have hLpG : ∀ i ∈ S, MemLp (fun ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P := by
    intro i hi
    exact hLp i hi
  have hResult :=
    avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
      Y hYν S s t G hst hSep hGown hGpair hLpG
  dsimp only at hResult
  exact hResult
