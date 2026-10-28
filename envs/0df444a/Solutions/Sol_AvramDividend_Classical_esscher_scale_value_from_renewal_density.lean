-- Prove2me | solution 1 for AvramDividend.Classical.esscher_scale_value_from_renewal_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:01:07.408444+00:00
-- url     : https://prove2.me/submissions/82cf5d47-5f84-475b-807f-2a56a3e353b8

import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_full_cumulative
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Convert a finite real-density renewal measure into the positive Esscher scale primitive. -/
theorem solution
    (W : ℝ → ℝ) (φ r : ℝ) (f : ℝ → ℝ)
    (hr : 0 ≤ r) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (hβneg : β (Iio (0 : ℝ)) = 0)
    (hβfin : β Set.univ ≠ ⊤)
    (hscale : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal)
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (x : ℝ) (hx : 0 < x) :
    W x = Real.exp (φ * x) *
      (r + r * ∫ y in (0 : ℝ)..x, f y) := by
  have hcum := geometric_atom_plus_real_density_full_cumulative
    r hr f hfpos β hβ hβneg hβfin x hx (hfi x hx)
  have hpoint :
      Real.exp (-(φ * x)) * W x =
        r + r * ∫ y in (0 : ℝ)..x, f y := by
    exact (hscale x hx).trans hcum
  have hexp : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    W x = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by
      rw [hexp, one_mul]
    _ = Real.exp (φ * x) * (Real.exp (-(φ * x)) * W x) := by
      rw [mul_assoc]
    _ = Real.exp (φ * x) *
          (r + r * ∫ y in (0 : ℝ)..x, f y) := by rw [hpoint]


