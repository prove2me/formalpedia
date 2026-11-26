-- Prove2me | solution 1 for FD1D.LocalHazard.p_le_N_add_half_a_mul_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:22.186899+00:00
-- url     : https://prove2.me/submissions/90d53240-29c2-4df1-aa30-f266b94368f7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (ht : t a p h x y ≤ h / 2) :
    p ≤ (N x y + a / 2) * h := by
  unfold t at ht
  have ht' := (div_le_iff₀ ha).mp ht
  simp only [q] at ht'
  nlinarith
end FD1D.LocalHazard
