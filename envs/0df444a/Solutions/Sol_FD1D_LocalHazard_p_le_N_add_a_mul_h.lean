-- Prove2me | solution 1 for FD1D.LocalHazard.p_le_N_add_a_mul_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:09.467954+00:00
-- url     : https://prove2.me/submissions/c56f287a-9c29-4501-8b68-c5a90b415daa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_p_le_N_add_half_a_mul_h

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    p ≤ (N x y + a) * h := by
  calc
    p ≤ (N x y + a / 2) * h := p_le_N_add_half_a_mul_h ha ht
    _ ≤ (N x y + a) * h := by
      apply mul_le_mul_of_nonneg_right _ hh
      linarith
end FD1D.LocalHazard
