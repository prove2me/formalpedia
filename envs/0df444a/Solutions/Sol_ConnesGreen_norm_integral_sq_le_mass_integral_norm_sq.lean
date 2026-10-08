-- Prove2me | solution 1 for ConnesGreen.norm_integral_sq_le_mass_integral_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T20:34:32.341229+00:00
-- url     : https://prove2.me/submissions/7db07267-24d8-430b-b20b-184e780ada07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory Set
noncomputable section

theorem solution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let m := μ.real univ
  let J := ∫ x, ‖f x‖ ∂μ
  let L := ∫ x, ‖f x‖ ^ 2 ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  have hJ : 0 ≤ J := integral_nonneg (fun x => norm_nonneg _)
  have hnorm : ‖∫ x, f x ∂μ‖ ≤ J := norm_integral_le_integral_norm f
  have hv : 0 ≤ ∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have he : (∫ x, (m * ‖f x‖ - J) ^ 2 ∂μ) = m ^ 2 * L - m * J ^ 2 := by
    simp_rw [show ∀ x, (m * ‖f x‖ - J) ^ 2 =
      m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖ + J ^ 2 by intro x; ring]
    have hd : Integrable (fun x => m ^ 2 * ‖f x‖ ^ 2 - (2 * m * J) * ‖f x‖) μ :=
      (hf2.const_mul _).sub (hf.norm.const_mul _)
    rw [integral_add hd (integrable_const _),
      integral_sub (hf2.const_mul _) (hf.norm.const_mul _), integral_const_mul,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul]
    dsimp [m, J, L]
    ring
  rw [he] at hv
  by_cases hm0 : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact ((ENNReal.toReal_eq_zero_iff (μ univ)).mp hm0).resolve_right
        (measure_ne_top μ univ)
    simp [hμ]
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hsq : J ^ 2 ≤ m * L := by nlinarith
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq
