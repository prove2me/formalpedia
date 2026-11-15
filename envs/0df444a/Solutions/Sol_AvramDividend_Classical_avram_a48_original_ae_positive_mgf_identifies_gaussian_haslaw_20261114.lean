-- Prove2me | solution 1 for AvramDividend.Classical.avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:46:41.589025+00:00
-- url     : https://prove2.me/submissions/6824d5cb-2877-45a9-b586-696ca120b6ce

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (v : ℝ≥0)
    (hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMGF : ∀ θ : ℝ, 0 < θ →
      mgf Z P θ = mgf id (gaussianReal 0 v) θ) :
    HasLaw Z (gaussianReal 0 v) P := by
  refine ⟨hZ, ?_⟩
  letI : IsProbabilityMeasure (Measure.map Z P) :=
    Measure.isProbabilityMeasure_map hZ
  apply measure_eq_of_pos_mgf_on_ray
  · intro θ hθ
    have hA : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) (Measure.map Z P) := by
      fun_prop
    exact (integrable_map_measure hA hZ).mpr (hInt θ hθ)
  · intro θ hθ
    exact integrable_exp_mul_gaussianReal θ
  · intro θ hθ
    have hA : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) (Measure.map Z P) := by
      fun_prop
    have hI := hMGF θ hθ
    simp only [mgf, id] at hI
    rw [integral_map hZ hA]
    exact hI
