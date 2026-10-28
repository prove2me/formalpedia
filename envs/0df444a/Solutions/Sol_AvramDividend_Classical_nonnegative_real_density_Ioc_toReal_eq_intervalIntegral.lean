-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:02:32.883765+00:00
-- url     : https://prove2.me/submissions/24cd443e-ee2a-45b1-97a0-20302b5c412a

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

/-- A nonnegative real density assigns its usual real interval integral to (0,x]. -/
theorem solution
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (x : ℝ) (hx : 0 ≤ x)
    (hfi : IntervalIntegrable f volume 0 x) :
    ((volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
      (Ioc (0 : ℝ) x)).toReal = ∫ y in (0 : ℝ)..x, f y := by
  have hloc : IntegrableOn f (Ioc (0 : ℝ) x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hfi
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc (0 : ℝ) x)] f :=
    Filter.Eventually.of_forall hfnn
  have hmass :
      (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
        (Ioc (0 : ℝ) x) =
      ENNReal.ofReal (∫ y in Ioc (0 : ℝ) x, f y ∂volume) := by
    rw [withDensity_apply _ measurableSet_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal hloc hnn).symm
  rw [hmass, ENNReal.toReal_ofReal (integral_nonneg hfnn)]
  exact (intervalIntegral.integral_of_le hx).symm
