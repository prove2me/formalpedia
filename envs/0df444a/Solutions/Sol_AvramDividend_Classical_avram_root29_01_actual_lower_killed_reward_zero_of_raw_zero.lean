-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:39:17.673998+00:00
-- url     : https://prove2.me/submissions/2b1da53b-d316-46ff-8c5b-5a39def9837f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- At lower first exit, an unrestricted nonnegative q-scale payoff
converging to zero forces the truly killed payoff to vanish as well. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (x : ℝ)
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hWnonneg : ∀ n, 0 ≤ W (x + X.X (t n) ω))
    (hRawZero : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds 0) := by
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) η)
  let B : ℕ → Set Ω := fun n => {η : Ω |
    ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}
  have hR0 (n : ℕ) : 0 ≤ R n ω := by
    change 0 ≤ Real.exp (-(q * (t n : ℝ))) *
      W (x + X.X (t n) ω)
    exact mul_nonneg (Real.exp_pos _).le (hWnonneg n)
  have hBounds (n : ℕ) :
      0 ≤ (B n).indicator (R n) ω ∧
      (B n).indicator (R n) ω ≤ R n ω := by
    by_cases hmem : ω ∈ B n
    · simpa only [Set.indicator_of_mem hmem] using
        (show 0 ≤ R n ω ∧ R n ω ≤ R n ω from ⟨hR0 n, le_rfl⟩)
    · simpa only [Set.indicator_of_notMem hmem] using
        (show 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ R n ω from ⟨le_rfl, hR0 n⟩)
  have hRaw : Tendsto (fun n => R n ω) atTop (nhds 0) := by
    simpa only [R] using hRawZero
  have hLo : (fun _ : ℕ => (0 : ℝ)) ≤
      (fun n => (B n).indicator (R n) ω) :=
    fun n => (hBounds n).1
  have hHi : (fun n => (B n).indicator (R n) ω) ≤
      (fun n => R n ω) :=
    fun n => (hBounds n).2
  have hLim := tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hRaw hLo hHi
  simpa only [R, B] using hLim
