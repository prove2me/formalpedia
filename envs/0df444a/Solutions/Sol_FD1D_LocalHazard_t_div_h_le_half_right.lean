-- Prove2me | solution 1 for FD1D.LocalHazard.t_div_h_le_half_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:57.916733+00:00
-- url     : https://prove2.me/submissions/b9be5928-bf0a-45a5-b071-c185f8a1c0e7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_hR_pos
import Theorems.Thm_FD1D_LocalHazard_tR_le_half_hR

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tR a p h x y / hR a h x y ≤ 1 / 2 := by
  have ht' : t a p h x y ≤ h / 2 := by
    apply (div_le_iff₀ hh).mp at ht
    linarith
  have hchild : 0 < hR a h x y := hR_pos ha hh
  apply (div_le_iff₀ hchild).2
  have := tR_le_half_hR ha hh.le ht'
  linarith
end FD1D.LocalHazard
