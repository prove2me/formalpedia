-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/893219e0-a722-4f6b-8698-033ccaf9a543

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzExponential_im
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo

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
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖stripSchwarzExponential ℓ z y - 1‖ := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  calc
    Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) =
      |(stripSchwarzExponential ℓ z y - 1).im| := by
        rw [Complex.sub_im, Complex.one_im, sub_zero,
          stripSchwarzExponential_im,
          abs_of_pos (mul_pos (Real.exp_pos _) hsin)]
    _ ≤ ‖stripSchwarzExponential ℓ z y - 1‖ :=
      Complex.abs_im_le_norm _
end CohnElkies
