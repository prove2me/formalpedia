-- Prove2me | solution 1 for CohnElkies.norm_stripRegularizedHolomorphicPoissonKernel_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/12732200-c97d-427d-8610-e95a53feca0c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_of_neg

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
    {y : ℝ} (hy : y < 0) :
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
      Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) :=
    Real.exp_pos _
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin hℓ hz y
  calc
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ =
      1 / (2 * ℓ * ‖stripSchwarzExponential ℓ z y - 1‖) := by
      rw [stripRegularizedHolomorphicPoissonKernel_of_neg
        hℓ hz hy, norm_div, norm_mul, norm_mul]
      simp [abs_of_pos hℓ]
    _ ≤ 1 /
        (2 * ℓ *
          (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
            Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)))) := by
      apply div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (mul_pos (by norm_num) hℓ)
          (mul_pos hexp hsin))
      exact mul_le_mul_of_nonneg_left hden
        (mul_pos (by norm_num) hℓ).le
    _ = Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
      rw [Real.exp_neg]
      field_simp [hℓ.ne', hexp.ne', hsin.ne']
end CohnElkies
