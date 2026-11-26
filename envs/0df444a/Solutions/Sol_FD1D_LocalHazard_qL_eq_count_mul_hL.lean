-- Prove2me | solution 1 for FD1D.LocalHazard.qL_eq_count_mul_hL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:22.043996+00:00
-- url     : https://prove2.me/submissions/7505786a-191d-43ad-b1d6-b1a24bfc3aa1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_q_mul_dL_eq_count_mul_hL

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    qL a h x y = (x : ℝ) * hL a h x y := by
  exact q_mul_dL_eq_count_mul_hL ha rfl
end FD1D.LocalHazard
