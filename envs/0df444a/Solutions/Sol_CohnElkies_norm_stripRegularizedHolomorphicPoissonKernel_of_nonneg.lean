-- Prove2me | solution 1 for CohnElkies.norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/73016f31-4fd0-4f45-a9e1-5bd5169828a9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_stripSchwarzExponential
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_stripSchwarzExponential_sub_one_norm_ge_sin
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_of_nonneg

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
    {y : ℝ} (hy : 0 ≤ y) :
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_sin hℓ hz y
  calc
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * ‖stripSchwarzExponential ℓ z y - 1‖) := by
      rw [stripRegularizedHolomorphicPoissonKernel_of_nonneg
        hℓ hz hy, norm_div, norm_mul, norm_mul,
        norm_stripSchwarzExponential]
      simp [abs_of_pos hℓ]
    _ ≤ Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le
        (mul_pos (mul_pos (by norm_num) hℓ) hsin)
      exact mul_le_mul_of_nonneg_left hden
        (mul_pos (by norm_num) hℓ).le
end CohnElkies
