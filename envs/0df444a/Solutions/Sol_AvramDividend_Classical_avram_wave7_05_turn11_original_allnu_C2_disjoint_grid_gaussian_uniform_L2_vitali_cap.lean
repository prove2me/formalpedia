-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_uniform_L2_vitali_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:05.981866+00:00
-- url     : https://prove2.me/submissions/b91edc26-523a-4136-bec1-2f4ad6385db8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Uniform finite-grid L² control for the actual stopped original-process gradient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hTotal : (∑ i ∈ S, ((t i - s i) : ℝ≥0) : ℝ) ≤ (T : ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
       else 0) *
      (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P)
    (hCell : ∀ i ∈ S,
      (∫ ω, ((if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
         else 0) *
        (Y.X (t i) ω - Y.X (s i) ω -
          ((t i - s i) : ℝ) * Y.c)) ^ 2 ∂P) ≤
        ((t i - s i) : ℝ) * X.σ ^ 2 * K ^ 2) :
    let G : ℕ → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ℕ → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    eLpNorm (fun ω => ∑ i ∈ S, F i ω) (2 : ℝ≥0∞) P ≤
      ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2)) := by
  classical
  let G : ℕ → Ω → ℝ := fun i ω =>
    if s i ≤ T then
      (Real.exp (-(q * (s i : ℝ))) *
        deriv w (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
      (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  let F : ℕ → Ω → ℝ := fun i ω =>
    G i ω * (Y.X (t i) ω - Y.X (s i) ω -
      ((t i - s i) : ℝ) * Y.c)
  have hGrid :=
    avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp x D hD w C hw q T
      S s t hst hSep hTotal K hK hLp hCell
  dsimp only at hGrid
  change eLpNorm (fun ω => ∑ i ∈ S, F i ω) (2 : ℝ≥0∞) P ≤
    ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2))
  have hB : 0 ≤ (T : ℝ) * X.σ ^ 2 * K ^ 2 := by positivity
  exact avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound
    P (fun ω => ∑ i ∈ S, F i ω)
      ((T : ℝ) * X.σ ^ 2 * K ^ 2) hB hGrid.1 hGrid.2
