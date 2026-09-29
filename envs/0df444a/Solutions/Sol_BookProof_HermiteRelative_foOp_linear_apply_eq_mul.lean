-- Prove2me | solution 1 for BookProof.HermiteRelative.foOp_linear_apply_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:04:56.679689+00:00
-- url     : https://prove2.me/submissions/7ac2ffe7-138d-40de-9ae4-e23bfcb83be4

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean -/
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
set_option autoImplicit false
open BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
variable {d : ℕ}
private theorem scout_pgFun_smul (r : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (r • p) x = r * pgFun p x := by
  simp [pgFun, MvPolynomial.smul_eval]
  ring
private theorem scout_pgFun_add (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (p + q) x = pgFun p x + pgFun q x := by
  simp [pgFun]
  ring
theorem solution (b : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (foPoly b 0 p) x = ((∑ i, b i * x i : ℝ) : ℂ) * pgFun p x := by
  classical
  have hpoly : foPoly b 0 p = ∑ i, ((b i : ℝ) : ℂ) • (X i * p) := by
    simp [foPoly, mulXPoly]
  rw [hpoly]
  have : pgFun (∑ i, ((b i : ℝ) : ℂ) • (X i * p)) x
      = ∑ i, ((b i : ℝ) : ℂ) * pgFun (X i * p) x := by
    classical
    induction (Finset.univ : Finset (Fin d)) using Finset.induction with
    | empty => simp [pgFun]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          scout_pgFun_add, ih,
          scout_pgFun_smul]
  rw [this]
  have hx : ∀ i : Fin d, pgFun ((X i : MvPolynomial (Fin d) ℂ) * p) x
      = ((x i : ℝ) : ℂ) * pgFun p x := fun i => by
    simp [pgFun, mul_assoc]
  simp_rw [hx]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
#print axioms solution
