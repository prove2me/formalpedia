-- Prove2me | solution 1 for FD1D.LocalHazard.N_div_N_add_two_mul_a_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:48.037804+00:00
-- url     : https://prove2.me/submissions/c53422d7-9040-42bf-8969-dc5f96a94014

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_nonneg
import Theorems.Thm_FD1D_LocalHazard_N_add_two_mul_a_pos

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 ≤ N x y / (N x y + 2 * a) := by
  exact div_nonneg (N_nonneg x y) (N_add_two_mul_a_pos ha x y).le
end FD1D.LocalHazard
