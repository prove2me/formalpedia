-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:41:35.836509+00:00
-- url     : https://prove2.me/submissions/f719776d-bb94-4dce-bd3b-549d48ec363c

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Original stopped pure-Gaussian drift-centred increment has real variance at most h sigma squared. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2 := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change (∫ ω, (Y ω) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2
  have hY : MemLp Y 2 P := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hτ T hbounded h
  have hSq : Integrable (fun ω => (Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY
  have hE :
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤
        ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
        X hν τ hτ T hbounded h
  have hI :
      ENNReal.ofReal (∫ ω, (Y ω) ^ 2 ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hSq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
  have hb : 0 ≤ (h : ℝ) * X.σ ^ 2 := by positivity
  have hC :
      ENNReal.ofReal (∫ ω, (Y ω) ^ 2 ∂P) ≤
        ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) := by
    rw [hI]
    exact hE
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp hC
