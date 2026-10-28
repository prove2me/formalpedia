-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_cutoff_canonical_analytic_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:38:01.921852+00:00
-- url     : https://prove2.me/submissions/fa472d2a-d58f-48ab-8b0e-5ca35ea4e473

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_contDiffOn_positive_below_cap
import Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_HJB_drift_neg_one
import Theorems.Thm_AvramDividend_Classical_positive_gaussian_standing_and_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (C : ℝ≥0∞) :
    X.Standing ∧ ¬ X.BoundedVariation ∧
    ContinuousOn (fun z : ℝ => if z < 0 then 0 else z - 1) (Ici (0 : ℝ)) ∧
    (∀ y : ℝ, y < 0 → (fun z : ℝ => if z < 0 then 0 else z - 1) y = 0) ∧
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1) {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
        X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y - (1 : ℝ) * (fun z : ℝ => if z < 0 then 0 else z - 1) y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y) := by
  obtain ⟨hStand, hBV⟩ := positive_gaussian_standing_and_unbounded_variation X hσ hI
  have hcont := affine_cutoff_continuous_nonnegative_smooth_positive.1
  refine ⟨hStand, hBV, hcont, ?_, affine_cutoff_contDiffOn_positive_below_cap C, ?_, ?_⟩
  · intro y hy
    simp [hy]
  · intro y hy _
    obtain ⟨hgen, hineq, _⟩ := zero_jump_affine_cutoff_HJB_drift_neg_one X hν hc y hy
    exact ⟨hgen, by simpa only [one_mul] using hineq⟩
  · intro y hy _
    exact (zero_jump_affine_cutoff_HJB_drift_neg_one X hν hc y hy).2.2
