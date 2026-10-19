-- Prove2me | solution 1 for CohnElkies.stripNormalizedPoissonKernel_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/450624e6-d8ab-476f-9d97-86cb5322b392

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo
import Theorems.Thm_CohnElkies_stripAngle_eq_pi_sub

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
    {σ : ℝ} (_hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    stripNormalizedPoissonKernel σ T =
      stripNormalizedPoissonExtension σ T := by
  have hsmall : Real.pi * (1 - σ) / 2 ≠ 0 := by
    exact ne_of_gt (div_pos (mul_pos Real.pi_pos (sub_pos.mpr habove))
      (by norm_num))
  have hmass : 1 - σ ≠ 0 := (sub_pos.mpr habove).ne'
  have hden :
      Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - σ) / 2) ≠ 0 := by
    have hangle := stripAngle_mem_Ioo _hbelow habove
    have horiginal :
        0 < Real.cosh (Real.pi * T / 2) -
          Real.cos (stripAngle σ) := by
      have hcos : Real.cos (stripAngle σ) < 1 := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi
          (x := 0) (y := stripAngle σ)
          (by norm_num) hangle.2.le hangle.1
        simpa using! h
      linarith [Real.one_le_cosh (Real.pi * T / 2)]
    rw [stripAngle_eq_pi_sub, Real.cos_pi_sub] at horiginal
    have hpositive :
        0 < Real.cosh (Real.pi * T / 2) +
          Real.cos (Real.pi * (1 - σ) / 2) := by
      simpa only [sub_neg_eq_add] using! horiginal
    exact hpositive.ne'
  unfold stripNormalizedPoissonKernel stripPoissonKernel
    stripBottomMass stripNormalizedPoissonExtension
  rw [stripAngle_eq_pi_sub, Real.sin_pi_sub, Real.cos_pi_sub,
    Real.sinc_of_ne_zero hsmall]
  field_simp [hmass, hsmall, hden, Real.pi_ne_zero]; ring
end CohnElkies
