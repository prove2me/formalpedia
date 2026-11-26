-- Prove2me | solution 1 for FD1D.LocalHazard.N_div_N_add_two_mul_a_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:38.248488+00:00
-- url     : https://prove2.me/submissions/c2baff39-b743-4351-9114-0cbf9d913d2b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_add_two_mul_a_pos

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    N x y / (N x y + 2 * a) ≤ 1 := by
  apply (div_le_one (N_add_two_mul_a_pos ha x y)).2
  linarith
end FD1D.LocalHazard
