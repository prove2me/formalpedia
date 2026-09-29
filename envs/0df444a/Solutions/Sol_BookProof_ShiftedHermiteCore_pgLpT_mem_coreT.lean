-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.pgLpT_mem_coreT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:25:05.878463+00:00
-- url     : https://prove2.me/submissions/97281951-5e2d-4386-8a8e-e5a2c9037728

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.pgLpT_mem_coreT
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    pgLpT a k p ∈ polyGaussCoreT a k := ⟨p, rfl⟩
