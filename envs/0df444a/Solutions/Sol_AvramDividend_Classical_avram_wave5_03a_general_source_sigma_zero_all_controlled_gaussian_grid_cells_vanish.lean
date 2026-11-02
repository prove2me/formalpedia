-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_all_controlled_gaussian_grid_cells_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:44:52.630601+00:00
-- url     : https://prove2.me/submissions/3ae9fa45-13c7-44fc-a266-62f427febad4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (S : Finset ι) (s : ι → ℝ≥0) (q K : ℝ)
    (τ : ι → Ω → ℝ≥0) (h : ι → ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    ∀ ω : Ω, (∑ i ∈ S,
      ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))) *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)) = 0 := by
  classical
  intro ω
  simp [hσ]
