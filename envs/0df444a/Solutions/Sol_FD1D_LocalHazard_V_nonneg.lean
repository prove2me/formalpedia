-- Prove2me | solution 1 for FD1D.LocalHazard.V_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:06.339892+00:00
-- url     : https://prove2.me/submissions/7d598d98-82c4-4b39-9524-ba07a4511250

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_D_pos
import Theorems.Thm_FD1D_LocalHazard_V_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 ≤ h) :
    0 ≤ V a h x y := by
  rw [V_eq ha]
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [D, N]
  · have hD := D_pos ha hne
    positivity
end FD1D.LocalHazard
