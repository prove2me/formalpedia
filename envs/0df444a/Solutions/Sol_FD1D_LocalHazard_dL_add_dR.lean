-- Prove2me | solution 1 for FD1D.LocalHazard.dL_add_dR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:27.005106+00:00
-- url     : https://prove2.me/submissions/cb69e05e-dfce-40f2-a06b-70ce30ef150a

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_D_ne_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} {x y : ℕ} (ha : 0 < a) :
    dL a x y + dR a x y = 1 := by
  by_cases hne : x + y = 0
  · norm_num [dL, dR, hne]
  · have hD := D_ne_zero ha hne
    simp only [dL, dR, if_neg hne]
    field_simp [hD]
    unfold D N
    ring
end FD1D.LocalHazard
