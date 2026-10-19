-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/c7fd2bc7-31ed-4e66-b9a1-865afd3086b2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripAngle_mem_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    0 < stripPoissonKernel σ T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ) (by norm_num) hangle'.le hangle
    simpa using! h
  have hden : 0 < Real.cosh (Real.pi * T / 2) -
      Real.cos (stripAngle σ) := by
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  exact div_pos hsin (mul_pos (by norm_num) hden)
end CohnElkies
