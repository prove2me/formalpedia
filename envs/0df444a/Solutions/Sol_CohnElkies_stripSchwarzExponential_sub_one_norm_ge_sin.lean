-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_sub_one_norm_ge_sin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/341449e8-da90-4ff7-8aa4-87720db5d1f2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzExponential_re
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
    Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖stripSchwarzExponential ℓ z y - 1‖ := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have htrig :=
    Real.sin_sq_add_cos_sq (Real.pi * (z.im + ℓ) / (2 * ℓ))
  have hsquare :
      Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2 ≤
        ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero,
      stripSchwarzExponential_re, stripSchwarzExponential_im]
    nlinarith [sq_nonneg
      (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) -
        Real.cos (Real.pi * (z.im + ℓ) / (2 * ℓ)))]
  nlinarith [norm_nonneg (stripSchwarzExponential ℓ z y - 1)]
end CohnElkies
