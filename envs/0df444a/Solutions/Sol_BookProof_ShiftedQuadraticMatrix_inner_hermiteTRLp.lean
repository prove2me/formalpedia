-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:02.637671+00:00
-- url     : https://prove2.me/submissions/74bab532-a599-4abc-9fa9-c93e3206a25a

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_QuadraticRotation_inner_pgLp_rotPoly
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp O a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by

  rw [hermiteTRLp, hermiteTRLp, hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_pgLpT, inner_pgLp_rotPoly hO]
