-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_L1_vanishing_under_measure_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:56:32.429466+00:00
-- url     : https://prove2.me/submissions/a2555c3e-d570-49c8-9efd-b0a63eb19ed7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (hμν : μ ≤ ν)
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ n, Integrable (E n) ν)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂ν) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ ω, ‖E n ω‖ ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hbound (n : ℕ) :
      0 ≤ (∫ ω, ‖E n ω‖ ∂μ) ∧
        (∫ ω, ‖E n ω‖ ∂μ) ≤
          (∫ ω, ‖E n ω‖ ∂ν) := by
    constructor
    · exact integral_nonneg (fun ω => norm_nonneg (E n ω))
    · exact integral_mono_measure hμν
        (Filter.Eventually.of_forall (fun ω => norm_nonneg (E n ω))) ((hEI n).norm)
  have hLower :
      ∀ᶠ n in atTop, (0 : ℝ) ≤ (∫ ω, ‖E n ω‖ ∂μ) :=
    Filter.Eventually.of_forall (fun n => (hbound n).1)
  have hUpper :
      ∀ᶠ n in atTop,
        (∫ ω, ‖E n ω‖ ∂μ) ≤
          (∫ ω, ‖E n ω‖ ∂ν) :=
    Filter.Eventually.of_forall (fun n => (hbound n).2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hEL1 hLower hUpper
