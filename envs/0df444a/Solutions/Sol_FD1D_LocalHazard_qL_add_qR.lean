-- Prove2me | solution 1 for FD1D.LocalHazard.qL_add_qR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:15.894075+00:00
-- url     : https://prove2.me/submissions/09d32f42-a50a-44bd-9b25-aa21d3fb9746

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_dL_add_dR

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qL a h x y + qR a h x y = q h x y := by
  rw [qL, qR, ← mul_add, dL_add_dR ha, mul_one]
end FD1D.LocalHazard
