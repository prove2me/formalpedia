-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:16:44.527863+00:00
-- url     : https://prove2.me/submissions/23484744-b20c-474f-8e3d-08cccd840647

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original zero-jump compensated Gaussian exponential increments are integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) -
        ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2))) P := by
  have hMeas : Measurable (fun z : ℝ =>
      Real.exp (θ * (z - ((t - s : ℝ≥0) : ℝ) * Y.c))) := by
    fun_prop
  have hId := (Y.stationaryIncrements s t hst).comp hMeas
  have hInt0 :=
    avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
      Y hν (t - s) θ hθ
  have hInt : Integrable (fun ω =>
      Real.exp (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c))) P := by
    exact hId.integrable_iff.mpr hInt0
  let A : ℝ := ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)
  have heq :
      (fun ω => Real.exp
        (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) - A)) =
      (fun ω => Real.exp (-A) * Real.exp
        (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  change Integrable (fun ω => Real.exp
    (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) - A)) P
  rw [heq]
  exact hInt.const_mul _
