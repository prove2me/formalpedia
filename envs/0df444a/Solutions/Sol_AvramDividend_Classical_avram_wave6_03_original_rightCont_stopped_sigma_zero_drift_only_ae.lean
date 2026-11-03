-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:57:08.6942+00:00
-- url     : https://prove2.me/submissions/26ba4edc-330d-43bc-961e-cfcaeee5d007

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stopped zero-volatility zero-jump Lévy increment is purely drift almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : X.σ = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) :
    ∀ᵐ ω ∂P,
      X.X (τ ω + h) ω - X.X (τ ω) ω = (h : ℝ) * X.c := by
  classical
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hYMem : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hτstop B hbounded h
  have hYsqI : Integrable (fun ω => Y ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hYMem.aestronglyMeasurable).mp hYMem
  have hVar : (∫ ω, Y ω ^ 2 ∂P) = (h : ℝ) * X.σ ^ 2 :=
    avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      X hν τ hτstop B hbounded h
  have hVarZero : (∫ ω, Y ω ^ 2 ∂P) = 0 := by
    simpa [hσ] using hVar
  have hSqZero : (fun ω => Y ω ^ 2) =ᵐ[P] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))) hYsqI).mp hVarZero
  filter_upwards [hSqZero] with ω hz
  have hYZero : Y ω = 0 := by
    apply (mul_self_eq_zero : Y ω * Y ω = 0 ↔ Y ω = 0).mp
    simpa only [pow_two] using hz
  exact sub_eq_zero.mp hYZero
