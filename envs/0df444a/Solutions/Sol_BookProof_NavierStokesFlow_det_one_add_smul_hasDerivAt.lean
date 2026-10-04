-- Prove2me | solution 1 for BookProof.NavierStokesFlow.det_one_add_smul_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T07:00:18.466885+00:00
-- url     : https://prove2.me/submissions/dc12e0fa-88db-4e0e-9b44-cff1060de44a

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

-- Direct proof from the registered statement using Mathlib.
theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  have hfun : (fun t : ℝ =>
      (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)).eval t) =
      (fun t : ℝ => (1 + t • A).det) := by
    funext t
    change (Polynomial.evalRingHom t)
      (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval t
      ((1 : Matrix (Fin 3) (Fin 3) (Polynomial ℝ)) i j +
        Polynomial.X * Polynomial.C (A i j)) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + t * A i j
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, Polynomial.eval_one]
    · simp only [Matrix.one_apply_ne hij, Polynomial.eval_zero]
  have htrace :
      (Polynomial.derivative
        (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C))).eval 0 =
        A.trace := Matrix.derivative_det_one_add_X_smul A
  have hderiv :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)).hasDerivAt (0 : ℝ)
  rw [htrace] at hderiv
  exact hfun ▸ hderiv

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
