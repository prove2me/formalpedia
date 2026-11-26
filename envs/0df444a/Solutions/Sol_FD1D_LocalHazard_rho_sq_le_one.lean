-- Prove2me | solution 1 for FD1D.LocalHazard.rho_sq_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:23.237685+00:00
-- url     : https://prove2.me/submissions/2d7eeca6-71ff-40b8-8222-e7f82f4bea6c

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {x y : ℕ} (hne : x + y ≠ 0) : rho x y ^ 2 ≤ 1 := by
  have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hN : 0 < N x y := N_pos hne
  unfold rho
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hN)).2
  have hxy : 0 ≤ (x : ℝ) * (y : ℝ) := mul_nonneg hx hy
  simp only [N]
  nlinarith
end FD1D.LocalHazard
