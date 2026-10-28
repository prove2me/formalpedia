-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_interval_primitive_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:25:33.425351+00:00
-- url     : https://prove2.me/submissions/d173590e-2b8d-42ca-8104-8aef6dc7bf06

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_positive_laplace_cumulative_real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- The interval primitive has the same positive-axis Laplace formula as its Ioc version. -/
theorem solution
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in (0 : ℝ)..x, f s)) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ s in (0 : ℝ)..x, f s)) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * f s) / θ := by
  have hprim := positive_laplace_primitive_integrable f θ hθ hf
  have hlap := positive_laplace_cumulative_real f θ hθ hf
  have heq :
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in (0 : ℝ)..x, f s)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s ∂volume)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    rw [intervalIntegral.integral_of_le (le_of_lt hx)]
  constructor
  · change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    exact hprim.congr heq.symm
  · exact (integral_congr_ae heq).trans hlap
