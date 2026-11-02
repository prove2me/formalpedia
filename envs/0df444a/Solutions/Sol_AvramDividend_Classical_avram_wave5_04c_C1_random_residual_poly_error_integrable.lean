-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_random_residual_poly_error_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:17:53.070976+00:00
-- url     : https://prove2.me/submissions/c8c5123f-c035-4c6c-ac52-792587a03a71

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_poly_primitive_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators
open AvramDividend.Classical

/-! Every random C1 jump decrement minus an exponential polynomial primitive
has a genuine Bochner expectation under the residual first moment. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hMeas : Measurable R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω) (hInt : Integrable R P)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (y : ℝ) :
    Integrable (fun ω => (w y - w (y - R ω)) -
      (∫ r in (0 : ℝ)..R ω,
        Polynomial.eval (Real.exp (-r)) p)) P := by
  have hwCont : Continuous w := hwC1.continuous
  have hMeasW : Measurable (fun ω => w y - w (y - R ω)) := by
    fun_prop
  have hW : Integrable (fun ω => w y - w (y - R ω)) P := by
    apply (hInt.norm.const_mul L).mono' hMeasW.aestronglyMeasurable
    filter_upwards [] with ω
    have hh := hLip y (y - R ω)
    have hEq : y - (y - R ω) = R ω := by ring
    simpa only [Real.norm_eq_abs, hEq] using hh
  have hPol :=
    avram_wave5_04c_nonnegative_random_poly_primitive_integrable
      R hMeas hNonneg p hp
  exact hW.sub hPol
