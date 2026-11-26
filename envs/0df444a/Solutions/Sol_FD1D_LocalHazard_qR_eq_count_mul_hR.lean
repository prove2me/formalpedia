-- Prove2me | solution 1 for FD1D.LocalHazard.qR_eq_count_mul_hR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:47.317352+00:00
-- url     : https://prove2.me/submissions/fa847ecc-235d-4c98-96ec-9f3a706e0511

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_q_mul_dR_eq_count_mul_hR

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qR a h x y = (y : ℝ) * hR a h x y := by
  exact q_mul_dR_eq_count_mul_hR ha rfl
end FD1D.LocalHazard
