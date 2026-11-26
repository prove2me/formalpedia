-- Prove2me | solution 1 for FD1D.LocalHazard.hazardIncrement_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:49.625811+00:00
-- url     : https://prove2.me/submissions/81eda8a0-8c38-406e-9eea-1d2387f3b97b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos
import Theorems.Thm_FD1D_LocalHazard_rho_sq_le_one
import Theorems.Thm_FD1D_LocalHazard_hazardIncrement_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    b a h x y ^ 2 / (2 * a ^ 2) ≤
      (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [hL, hR, b, qL, qR, q, dL, dR, N]
  · have hN : 0 < N x y := N_pos hne
    have hrho := rho_sq_le_one hne
    have haN : 0 ≤ a / N x y := (div_pos ha hN).le
    have hfactor :
        (1 : ℝ) / 2 ≤ (3 - rho x y ^ 2) / 4 + a / N x y := by
      linarith
    have hba : 0 ≤ b a h x y ^ 2 / a ^ 2 := by positivity
    rw [hazardIncrement_eq ha]
    calc
      b a h x y ^ 2 / (2 * a ^ 2) =
          (b a h x y ^ 2 / a ^ 2) * (1 / 2) := by ring
      _ ≤ (b a h x y ^ 2 / a ^ 2) *
          ((3 - rho x y ^ 2) / 4 + a / N x y) :=
        mul_le_mul_of_nonneg_left hfactor hba
end FD1D.LocalHazard
