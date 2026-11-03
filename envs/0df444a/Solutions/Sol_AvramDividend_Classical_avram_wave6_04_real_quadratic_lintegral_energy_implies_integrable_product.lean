-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_real_quadratic_lintegral_energy_implies_integrable_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:34:13.19369+00:00
-- url     : https://prove2.me/submissions/1dca161c-3e89-44e8-821b-33be190ad47a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- Finite real quadratic lintegral energy gives an integrable quadratic product. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (hfin : (∫⁻ a, ENNReal.ofReal ((f a) ^ 2) ∂μ) < ⊤) :
    Integrable (fun a => f a * f a) μ := by
  classical
  have hNormEq : (fun a : α => ‖(f a) ^ 2‖ₑ) =
      (fun a => ENNReal.ofReal ((f a) ^ 2)) := by
    funext a
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hHas : HasFiniteIntegral (fun a => (f a) ^ 2) μ := by
    rw [hasFiniteIntegral_def]
    simpa only [hNormEq] using hfin
  have hInt : Integrable (fun a => (f a) ^ 2) μ :=
    ⟨(hf.pow_const 2).aestronglyMeasurable, hHas⟩
  simpa only [pow_two] using hInt