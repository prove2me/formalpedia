-- Prove2me | solution 1 for D1Bound5.coherent_quadratic_four_value_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:05.039313+00:00
-- url     : https://prove2.me/submissions/89424034-f4a2-4a1d-8a70-fe4e148e28e1

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions

section
open Finset Polynomial

namespace D1Bound5









/-- Four distinct prescribed product-square values determine the
three lower coefficients of the monic quartic.  This is the algebraic
core of simultaneous triple-form nonvanishing. -/
theorem _root_.solution
    {F : Type*} [Field F] (a R : Fin 4 → F) (hinj : Function.Injective a)
    (p q z v w : F) (hz : z^2 = p*q+1)
    (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hJ : ∀ i, z*(a i)^2+v*a i+w = a i*R i) :
    w^2 = coherentElementary4 a ∧
    2*v*w = -coherentElementary3 a ∧
    v^2+2*z*w-1 = coherentElementary2 a := by
  let e1 := a 0+a 1+a 2+a 3
  let e2 := coherentElementary2 a
  let e3 := coherentElementary3 a
  let e4 := coherentElementary4 a
  let G : F[X] := C (2*z*v-(p+q)+e1) * X^3 + C (v^2+2*z*w-1-e2) * X^2 +
    C (2*v*w+e3) * X + C (w^2-e4)
  have hexpand (x : F) : G.eval x =
      (z*x^2+v*x+w)^2 - x^2*(p*x+1)*(q*x+1) -
        (x-a 0)*(x-a 1)*(x-a 2)*(x-a 3) := by
    simp only [G, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    dsimp [e1, e2, e3, e4, coherentElementary2, coherentElementary3, coherentElementary4]
    linear_combination -x^4 * hz
  have heval (i : Fin 4) : G.eval (a i) = 0 := by
    rw [hexpand, hJ i]
    have hprod : (a i-a 0)*(a i-a 1)*(a i-a 2)*(a i-a 3) = 0 := by
      fin_cases i <;> simp
    rw [hprod]
    linear_combination (a i)^2 * hR i
  have hdegree : G.degree < ((Finset.univ : Finset (Fin 4)).card : WithBot ℕ) := by
    norm_num only [Finset.card_univ, Fintype.card_fin]
    dsimp [G]
    compute_degree <;> norm_num
  have hzero : G = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
      hinj.injOn hdegree (fun i _ => heval i)
  have h0 := congrArg (fun g : F[X] => g.coeff 0) hzero
  have h1 := congrArg (fun g : F[X] => g.coeff 1) hzero
  have h2 := congrArg (fun g : F[X] => g.coeff 2) hzero
  simp only [G, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h0 h1 h2
  norm_num at h0 h1 h2
  dsimp only [e2, e3, e4] at h0 h1 h2
  exact ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2⟩







end D1Bound5
end
