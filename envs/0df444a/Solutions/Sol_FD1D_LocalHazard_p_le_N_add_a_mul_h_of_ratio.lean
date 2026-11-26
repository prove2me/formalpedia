-- Prove2me | solution 1 for FD1D.LocalHazard.p_le_N_add_a_mul_h_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:55:05.18202+00:00
-- url     : https://prove2.me/submissions/fccf245e-34e2-4cd9-8643-af8335168cd2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_p_le_N_add_a_mul_h

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    p ≤ (N x y + a) * h := by
  apply p_le_N_add_a_mul_h ha hh.le
  have ht' := (div_le_iff₀ hh).mp ht
  linarith
end FD1D.LocalHazard
