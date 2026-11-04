-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:41.806463+00:00
-- url     : https://prove2.me/submissions/df95bde5-9a6e-423f-b875-055d3b5b3a3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual finite ruin clock is q-discounted source exponential L1 for every q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by
  have hclock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    exact hclock.2.1 ω
  exact avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
    X θ hθ q τ hτmeas hτstop n hbound
