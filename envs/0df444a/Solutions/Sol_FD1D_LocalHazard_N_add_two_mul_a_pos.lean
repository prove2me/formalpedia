-- Prove2me | solution 1 for FD1D.LocalHazard.N_add_two_mul_a_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:39.845909+00:00
-- url     : https://prove2.me/submissions/98e68ce3-7962-4ebe-8673-b3a1296c5dff

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_nonneg

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 < N x y + 2 * a := by
  have hN := N_nonneg x y
  linarith
end FD1D.LocalHazard
