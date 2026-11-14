-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB263_positive_mgf_identity_implies_gaussian_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:50:46.635875+00:00
-- url     : https://prove2.me/submissions/bb241baf-73cb-467c-9c47-514d1691760a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive-ray moment generating functions identify a Gaussian pushforward law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (m : ℝ) (v : ℝ≥0)
    (hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMGF : ∀ θ : ℝ, 0 < θ →
      mgf Z P θ = mgf id (gaussianReal m v) θ) :
    Measure.map Z P = gaussianReal m v := by
  letI : IsProbabilityMeasure (Measure.map Z P) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  apply measure_eq_of_pos_mgf_on_ray
  · intro θ hθ
    have hA : AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y))
        (Measure.map Z P) := by fun_prop
    exact (integrable_map_measure hA hZ.aemeasurable).mpr
      (hInt θ hθ)
  · intro θ hθ
    exact integrable_exp_mul_gaussianReal θ
  · intro θ hθ
    have hA : AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y))
        (Measure.map Z P) := by fun_prop
    have hI := hMGF θ hθ
    simp only [mgf, id] at hI
    rw [integral_map hZ.aemeasurable hA]
    exact hI

-- Rebased the existing complete positive-ray MGF uniqueness proof for the current checker.
