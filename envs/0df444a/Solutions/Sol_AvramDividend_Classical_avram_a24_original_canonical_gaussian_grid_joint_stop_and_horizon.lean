-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:13:44.794797+00:00
-- url     : https://prove2.me/submissions/a38de52a-67cd-4c8f-9810-6194ca5ec2ac

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original stopped Gaussian time grid is uniformly bounded and adapted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let τg : ℕ → ℕ → Ω → ℝ≥0 := fun j i ω =>
      min ((i : ℝ≥0) * ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ ω)
    (∀ j i (t : ℝ≥0),
      MeasurableSet[𝓕.rightCont t] {ω : Ω | τg j i ω ≤ t}) ∧
    (∀ j i ω, τg j i ω ≤ (n : ℝ≥0)) ∧
    (∀ j i ω, τg j i ω ≤ σ ω):= by
  dsimp
  constructor
  · intro j i t
    have hstop :=
      (avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
        σ hσstop n j i).1
    simpa only [WithTop.coe_le_coe] using
      (hstop.measurableSet_le t)
  constructor
  · intro j i ω
    exact ((avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
      σ hσstop n j i).2.2 ω).trans (hBound ω)
  · intro j i ω
    exact (avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
      σ hσstop n j i).2.2 ω
