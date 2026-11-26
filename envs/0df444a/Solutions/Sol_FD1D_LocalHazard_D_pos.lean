-- Prove2me | solution 1 for FD1D.LocalHazard.D_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:39.135936+00:00
-- url     : https://prove2.me/submissions/ff36e9bc-6540-4a24-93d0-b6429942d9c1

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} {x y : ℕ} (ha : 0 < a) (hne : x + y ≠ 0) :
    0 < D a x y := by
  have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hN : 0 < N x y := N_pos hne
  unfold D
  positivity
end FD1D.LocalHazard
