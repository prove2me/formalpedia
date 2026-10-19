-- Prove2me | solution 1 for CohnElkies.stripAngle_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/184909e4-6334-4b6f-a4a9-441f3ee49cd5

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripAngle σ ∧ stripAngle σ < Real.pi := by
  unfold stripAngle
  constructor
  · exact div_pos (mul_pos Real.pi_pos (by linarith)) (by norm_num)
  · calc
      Real.pi * (1 + σ) / 2 < Real.pi * 2 / 2 := by
        gcongr
        linarith
      _ = Real.pi := by ring
end CohnElkies
