-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_uniform_discounted_exp_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:38.791015+00:00
-- url     : https://prove2.me/submissions/e6f9cf7b-047f-4a8f-b5df-2b70be46cd7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact ruin-truncated clock quantitative Esscher expectation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
      Real.exp (|X.ψ θ - q| * (n : ℝ)) := by
  have hclock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact hclock.2.1 ω
  simpa using
    (avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
      X θ hθ q τ hτstop n hbound)