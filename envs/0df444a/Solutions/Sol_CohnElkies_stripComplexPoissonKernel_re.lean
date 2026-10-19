-- Prove2me | solution 1 for CohnElkies.stripComplexPoissonKernel_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/6231f2fa-60a9-4f38-bb56-b26b5604f6c8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    (stripComplexPoissonKernel σ T).re =
      stripPoissonKernel σ T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < Real.exp (Real.pi * T / 2) := Real.exp_pos _
  have htrig := Real.sin_sq_add_cos_sq (stripAngle σ)
  have hden :
      0 < Real.exp (Real.pi * T / 2) ^ 2 + 1 -
        2 * Real.exp (Real.pi * T / 2) * Real.cos (stripAngle σ) := by
    nlinarith [sq_nonneg
      (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)),
      sq_pos_of_pos hsin]
  unfold stripComplexPoissonKernel stripPoissonKernel
  rw [Real.cosh_eq, Real.exp_neg]
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, Complex.add_re,
    Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.mul_im,
    sub_self, add_zero, zero_add, mul_zero,
    Complex.normSq_apply]
  norm_num
  field_simp [hexp.ne', hden.ne']
  nlinarith
end CohnElkies
