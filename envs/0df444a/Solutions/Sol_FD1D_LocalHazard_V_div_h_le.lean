-- Prove2me | solution 1 for FD1D.LocalHazard.V_div_h_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:14.669542+00:00
-- url     : https://prove2.me/submissions/e2fe2fef-03d0-4e67-bdc5-6005b0b27d74

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_normalizedV_le
import Theorems.Thm_FD1D_LocalHazard_V_div_h_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h ≤ N x y / (2 * a) := by
  rw [V_div_h_eq ha hh]
  exact normalizedV_le ha
end FD1D.LocalHazard
