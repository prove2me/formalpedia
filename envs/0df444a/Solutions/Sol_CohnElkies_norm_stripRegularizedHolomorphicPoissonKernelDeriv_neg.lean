-- Prove2me | solution 1 for CohnElkies.norm_stripRegularizedHolomorphicPoissonKernelDeriv_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/f94931e4-2686-46d2-9126-0aa4a1802ea4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_stripSchwarzExponential
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (y : ℝ) :
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ ≤
      Real.pi * Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp :
      0 < Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) :=
    Real.exp_pos _
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin hℓ hz y
  have hsq :
      (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) ^ 2 ≤
        ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2 := by
    exact
      (sq_le_sq₀ (mul_pos hexp hsin).le
        (norm_nonneg (stripSchwarzExponential ℓ z y - 1))).2 hden
  calc
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ =
      Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2) := by
      unfold stripRegularizedHolomorphicPoissonKernelDeriv
      rw [norm_div, norm_neg, norm_mul, norm_mul,
        norm_mul, norm_mul, norm_pow, norm_pow,
        norm_stripSchwarzExponential]
      simp [Real.norm_eq_abs, abs_of_pos hℓ,
        abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
            Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) ^ 2) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
        (by positivity)
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Real.pi * Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
      rw [Real.exp_neg]
      field_simp [hℓ.ne', hexp.ne', hsin.ne']
end CohnElkies
