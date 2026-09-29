-- Prove2me | solution 1 for BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:17:26.913965+00:00
-- url     : https://prove2.me/submissions/a13dcfc2-f311-40f9-bc8d-deae7bc162a7

-- Generated from ChapterHyperbolicQuadraticEsa.lean — solution of BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_essentiallySelfAdjoint
open BookProof.HyperbolicQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n)) (quadOp (minkowskiCoeff n)) := quadOp_essentiallySelfAdjoint _
