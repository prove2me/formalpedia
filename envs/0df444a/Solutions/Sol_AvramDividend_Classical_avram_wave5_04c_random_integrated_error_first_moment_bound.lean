-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_random_integrated_error_first_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:49:48.079568+00:00
-- url     : https://prove2.me/submissions/add1c3c7-0cb5-40c8-abd7-ee47a8deb6eb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory

/-! Integrate a pointwise C1 finite-band approximation error and retain
its exact full-residual and large-residual first-moment weights. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R E : Ω → ℝ) (M ε L : ℝ)
    (hER : Integrable E P) (hRR : Integrable R P)
    (hTail : Integrable (fun ω => if M < R ω then R ω else 0) P)
    (hPoint : ∀ᵐ ω ∂P,
      |E ω| ≤ ε * R ω +
        (2 * L + ε) * (if M < R ω then R ω else 0)) :
    |∫ ω, E ω ∂P| ≤
      ε * (∫ ω, R ω ∂P) +
        (2 * L + ε) *
          (∫ ω, if M < R ω then R ω else 0 ∂P) := by
  have hBoundInt : Integrable
      (fun ω => ε * R ω +
        (2 * L + ε) * (if M < R ω then R ω else 0)) P :=
    (hRR.const_mul ε).add (hTail.const_mul (2 * L + ε))
  calc
    |∫ ω, E ω ∂P| = ‖∫ ω, E ω ∂P‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖E ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (ε * R ω +
          (2 * L + ε) * (if M < R ω then R ω else 0)) ∂P := by
      apply integral_mono_ae hER.norm hBoundInt
      filter_upwards [hPoint] with ω hω
      simpa only [Real.norm_eq_abs] using hω
    _ = ε * (∫ ω, R ω ∂P) +
        (2 * L + ε) *
          (∫ ω, if M < R ω then R ω else 0 ∂P) := by
      rw [integral_add (hRR.const_mul ε)
        (hTail.const_mul (2 * L + ε)), integral_const_mul, integral_const_mul]
