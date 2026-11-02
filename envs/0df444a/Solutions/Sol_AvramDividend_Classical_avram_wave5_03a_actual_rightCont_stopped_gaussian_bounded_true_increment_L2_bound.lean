-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:41:31.607285+00:00
-- url     : https://prove2.me/submissions/95a6a141-f3b9-4eb3-9fcc-05b55e5651a8

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Bounded adapted or predictable multipliers preserve finite L2 source-increment energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
      K ^ 2 * (∫ ω, (Y ω) ^ 2 ∂P) := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
    K ^ 2 * (∫ ω, (Y ω) ^ 2 ∂P)
  have hY : MemLp Y 2 P := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hτ T hbounded h
  have hSq : Integrable (fun ω => (Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mp hY
  have hTop : Integrable (fun ω => K ^ 2 * (Y ω) ^ 2) P :=
    hSq.const_mul (K ^ 2)
  have hpoint (ω : Ω) :
      (H ω * Y ω) ^ 2 ≤ K ^ 2 * (Y ω) ^ 2 := by
    have hHa := abs_le.mp (hH ω)
    have hHsq : (H ω) ^ 2 ≤ K ^ 2 := by
      have hp : 0 ≤ (K - H ω) * (K + H ω) :=
        mul_nonneg (sub_nonneg.mpr hHa.2) (by linarith)
      nlinarith
    calc
      _ = (H ω) ^ 2 * (Y ω) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHsq (sq_nonneg _)
  calc
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
        (∫ ω, K ^ 2 * (Y ω) ^ 2 ∂P) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        hTop
        (Filter.Eventually.of_forall hpoint)
    _ = K ^ 2 * (∫ ω, (Y ω) ^ 2 ∂P) := by
      rw [integral_const_mul]