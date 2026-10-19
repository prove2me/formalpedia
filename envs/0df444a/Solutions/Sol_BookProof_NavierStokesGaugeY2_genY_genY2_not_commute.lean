-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY_genY2_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:16.541621+00:00
-- url     : https://prove2.me/submissions/89bdc627-8974-4347-b76a-54468ee90add

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY_genY2_not_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY_genY2_bracket_X_u
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : ⁅genY j, genY2 j⁆ ≠ 0 := by

  intro h
  have h0 : ⁅genY j, genY2 j⁆ (X (NSVar.u 0)) = 0 := by rw [h]; simp
  rw [genY_genY2_bracket_X_u 0 j, neg_eq_zero] at h0
  exact X_ne_zero (R := ℂ) (NSVar.uL 0) h0
