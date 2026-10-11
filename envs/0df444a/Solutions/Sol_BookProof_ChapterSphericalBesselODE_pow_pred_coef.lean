-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.pow_pred_coef
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:36.593258+00:00
-- url     : https://prove2.me/submissions/83f628ae-db77-48fa-a2e6-543555bad8e9

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.pow_pred_coef
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (l : ℝ) * r ^ (l - 1) = r ^ l * ((l : ℝ) / r) := by

  cases l with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      field_simp
