-- Prove2me | solution 1 for BookProof.QuadraticRotation.eval_rotPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:08:22.607839+00:00
-- url     : https://prove2.me/submissions/19042102-f277-4948-aa4b-19555176c731

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.eval_rotPoly
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_X
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
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly O p)
      = MvPolynomial.eval (fun i => (((rotIso hO x) i : ℝ) : ℂ)) p := by

  induction p using MvPolynomial.induction_on with
  | C a => simp [rotPoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, rotPoly_X, hp]
      simp [Complex.ofReal_sum]
