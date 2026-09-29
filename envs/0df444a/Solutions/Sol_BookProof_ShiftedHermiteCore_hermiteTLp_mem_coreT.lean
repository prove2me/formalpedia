-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.hermiteTLp_mem_coreT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:19.628667+00:00
-- url     : https://prove2.me/submissions/a74d680a-364e-453a-84d5-a83d933cd92e

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.hermiteTLp_mem_coreT
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgLpT_mem_coreT
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
theorem solution (a k : Vd d) (α : Fin d →₀ ℕ) :
    hermiteTLp a k α ∈ polyGaussCoreT a k := Submodule.smul_mem _ _ (pgLpT_mem_coreT a k _)
