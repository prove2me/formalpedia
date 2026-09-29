-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:54:45.233987+00:00
-- url     : https://prove2.me/submissions/7de43a6e-344a-4c90-b982-a9d453489636

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_le
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_norm_P_sq_le
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution (v : L.D) (i : Fin 3) {eps : ℝ} (heps : 0 < eps) :
    ‖(L.P i v : F)‖ ≤ eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖ := by

  set A : ℝ := ‖(v : F)‖ with hA
  set B : ℝ := ‖(secondOrder L v : F)‖ with hB
  set x : ℝ := ‖(L.P i v : F)‖ with hx
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hx0 : 0 ≤ x := norm_nonneg _
  have hsq : x ^ 2 ≤ 2 * (A * B) := norm_P_sq_le L v i
  have hR0 : 0 ≤ eps * B + (1 / (2 * eps)) * A := by positivity
  have hamgm : 2 * (A * B) ≤ (eps * B + (1 / (2 * eps)) * A) ^ 2 := by
    have h := sq_nonneg (eps * B - (1 / (2 * eps)) * A)
    have he : eps * (1 / (2 * eps)) = 1 / 2 := by field_simp
    nlinarith [h, he]
  nlinarith [hsq, hamgm, hR0, hx0]
