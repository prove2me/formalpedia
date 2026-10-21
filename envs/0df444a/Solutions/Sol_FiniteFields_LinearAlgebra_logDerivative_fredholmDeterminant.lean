-- Prove2me | solution 1 for FiniteFields.LinearAlgebra.logDerivative_fredholmDeterminant
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:52:59.367992+00:00
-- url     : https://prove2.me/submissions/856b40c3-8bed-446a-b435-7f00706fb528

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula
section
noncomputable section
open Module Polynomial PowerSeries
namespace FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
private theorem derivative_det {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R[X]) :
    A.det.derivative =
      ∑ j, (A.updateCol j fun i => (A i j).derivative).det := by
  rw [Matrix.det_apply', map_sum]
  simp_rw [Polynomial.derivative_mul, Polynomial.derivative_intCast, zero_mul, zero_add,
    Polynomial.derivative_prod_finset]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  simp only [Matrix.updateCol_apply, Finset.prod_ite]
  rw [mul_comm]
  congr 1
  · have hsingle : Finset.univ.filter (fun x : ι => x = j) = {j} := by
      ext i
      simp
    rw [hsingle, Finset.prod_singleton]
  · apply Finset.prod_congr
    · ext i
      simp [eq_comm]
    · simp
private theorem derivative_det_eq_trace_adjugate {ι : Type w} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R[X]) :
    A.det.derivative =
      Matrix.trace (A.adjugate *
        Matrix.of fun i j => (A i j).derivative) := by
  rw [derivative_det]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl
theorem fredholmDeterminant_eq_det (u : Module.End R M) {ι : Type w}
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    fredholmDeterminant u =
      Matrix.det (1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C) := by
  rw [fredholmDeterminant, ← LinearMap.charpoly_toMatrix u b,
    Matrix.reverse_charpoly, Matrix.charpolyRev]
theorem neg_derivative_fredholmDeterminant_eq_trace_adjugate (u : Module.End R M)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    -(fredholmDeterminant u).derivative =
      Matrix.trace
        ((1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C).adjugate *
          (LinearMap.toMatrix b b u).map Polynomial.C) := by
  rw [fredholmDeterminant_eq_det u b, derivative_det_eq_trace_adjugate]
  let A : Matrix ι ι R := LinearMap.toMatrix b b u
  let B : Matrix ι ι R[X] := 1 - (X : R[X]) • A.map Polynomial.C
  change -Matrix.trace (B.adjugate * Matrix.of fun i j => (B i j).derivative) =
    Matrix.trace (B.adjugate * A.map Polynomial.C)
  have hderiv : (Matrix.of fun i j => (B i j).derivative) = -(A.map Polynomial.C) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [B, Matrix.one_apply, Matrix.smul_apply, hij]
  rw [hderiv, Matrix.mul_neg, Matrix.trace_neg, neg_neg]
section FiniteRank
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
end FiniteRank
end FiniteFields.LinearAlgebra
end
end
open Module Polynomial PowerSeries
open FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
theorem solution (u : Module.End R M)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    fredholmLogDerivative u =
      ((Matrix.trace
          ((1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C).adjugate *
            (LinearMap.toMatrix b b u).map Polynomial.C) : R[X]) : R⟦X⟧) *
        PowerSeries.invOfUnit (fredholmDeterminant u : R⟦X⟧) 1 := by
  rw [fredholmLogDerivative, PowerSeries.derivative_coe]
  congr 1
  exact congrArg (fun p : R[X] => (p : R⟦X⟧))
    (neg_derivative_fredholmDeterminant_eq_trace_adjugate u b)
