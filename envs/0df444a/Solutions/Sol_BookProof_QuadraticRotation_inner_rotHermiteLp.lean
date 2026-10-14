-- Prove2me | solution 1 for BookProof.QuadraticRotation.inner_rotHermiteLp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T13:16:52.157989+00:00
-- url     : https://prove2.me/submissions/eba65aba-277f-4ead-a5f5-babb8f69ee21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.inner_rotHermiteLp
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_inner_pgLp_rotPoly
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a b : Fin d →₀ ℕ) :
    (inner ℂ (rotHermiteLp O a) (rotHermiteLp O b) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) a) (hermiteMvLp (d := d) b) : ℂ) := by

  rw [rotHermiteLp, rotHermiteLp, hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right, inner_pgLp_rotPoly hO]
