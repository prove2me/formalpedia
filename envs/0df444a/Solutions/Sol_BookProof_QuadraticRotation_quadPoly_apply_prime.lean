-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadPoly_apply_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T15:12:05.54174+00:00
-- url     : https://prove2.me/submissions/6ad31eef-9918-44cc-8706-522838eb2b88

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadPoly_apply'
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
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
theorem solution (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPoly c p = ∑ i, ((c i : ℝ) : ℂ) •
      (momPoly i (momPoly i p) + (1/4 : ℂ) • (X i * (X i * p))) := by

  -- The platform's published def bundles STRIP the theorem `mulXPoly_apply`
  -- (`@[simp]` in the workspace, a `Thm_*` node on the platform), so the local
  -- `simp [quadPoly, oscPoly]` closes here and leaves `mulXPoly i ?x` unreduced
  -- there.  Reduce term by term instead: each summand is definitionally equal.
  rw [quadPoly, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl
