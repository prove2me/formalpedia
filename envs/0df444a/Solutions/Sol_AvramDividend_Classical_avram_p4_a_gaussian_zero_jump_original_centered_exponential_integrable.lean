-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:31:40.949779+00:00
-- url     : https://prove2.me/submissions/f095cb06-b29e-4c26-9e72-71bf5cd396d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every positive exponential of a drift-centred original zero-jump Levy
process is integrable at deterministic time, directly from the source
Laplace hypothesis. No Brownian identification is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c))) P := by
  have hLap : Integrable (fun ω => Real.exp (θ * Y.X t ω)) P :=
    (Y.laplace t θ hθ).1
  have heq :
      (fun ω => Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c))) =
      (fun ω => Real.exp (-θ * (t : ℝ) * Y.c) *
        Real.exp (θ * Y.X t ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hLap.const_mul _
