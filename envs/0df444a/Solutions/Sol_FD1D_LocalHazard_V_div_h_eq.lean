-- Prove2me | solution 1 for FD1D.LocalHazard.V_div_h_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:21.378306+00:00
-- url     : https://prove2.me/submissions/2e11d24c-eb1d-4c84-9192-299c23449cfa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_V_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    V a h x y / h =
      ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by
  rw [V_eq ha]
  field_simp [hh.ne']
end FD1D.LocalHazard
