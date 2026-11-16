-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_centred_gaussianReal_square_integral_public_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:06:35.477576+00:00
-- url     : https://prove2.me/submissions/b520877a-7fb4-44dc-9a7a-3c20bcd7ba82

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- The second moment of a centred Gaussian is its variance parameter. -/
theorem solution (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) ∧
      (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hLp : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal 2
  have hInt : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp hLp
  have hVar : Var[id; gaussianReal (0 : ℝ) v] = (v : ℝ) :=
    variance_id_gaussianReal
  rw [variance_eq_integral (X := id) (μ := gaussianReal (0 : ℝ) v) measurable_id'.aemeasurable] at hVar
  simp [id, integral_id_gaussianReal] at hVar
  exact ⟨hInt, hVar⟩
