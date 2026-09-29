-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.norm_sqSumPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:49:38.800025+00:00
-- url     : https://prove2.me/submissions/47552b82-5cb4-43b3-b113-42da6e9f0ed7

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.norm_sqSumPoly_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_sqSumPoly_apply
import Theorems.Thm_BookProof_SqSumFarisLavine_norm_potPoly_mul_le
import Theorems.Thm_BookProof_GaussCoreQuadBounds_shiftNorm_nonneg
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_weighted_kin_le
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_kinPoly_le_shiftNorm
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_harmPoly_mul_le_shiftNorm
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (sqSumPoly kappa v p)‖ ≤ (3 / 2 * km + 8 * B) * shiftNorm p := by

  have hsplit : pgLp (sqSumPoly kappa v p)
      = pgLp (kinPart kappa p) + pgLp (potPoly v * p) := by
    rw [sqSumPoly_apply, ← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have hkin : ‖pgLp (kinPart kappa p)‖ ≤ km / 2 * ‖pgLp (kinPoly p)‖ :=
    norm_weighted_kin_le (kappa := fun j => -(kappa j) / 2) (km := km / 2) (by linarith)
      (fun j => by
        have h := abs_le.mp (hk j)
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]) p
  have h1 : ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := norm_kinPoly_le_shiftNorm p
  have h2 : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := norm_harmPoly_mul_le_shiftNorm p
  have hpot := norm_potPoly_mul_le hB0 hB p
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg (pgLp (kinPoly p)), norm_nonneg (pgLp (harmPoly * p)),
    shiftNorm_nonneg p]
