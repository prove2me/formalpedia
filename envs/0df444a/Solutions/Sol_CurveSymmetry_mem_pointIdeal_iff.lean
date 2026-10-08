-- Prove2me | solution 1 for CurveSymmetry.mem_pointIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:13.846068+00:00
-- url     : https://prove2.me/submissions/f24d7887-d58b-4b96-a28c-1d8e9f4150af

-- Solution generated from lean/OrdinaryMultiplePoints.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_C (x y c : ℂ) : planeEval x y (C c) = c := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_zero (x y : ℂ) : planeEval x y (X 0) = x := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_one (x y : ℂ) : planeEval x y (X 1) = y := by simp [planeEval]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (P : BPoly) (x y : ℂ) :
    P ∈ pointIdeal x y ↔ planeEval x y P = 0 := by
  constructor
  · intro hP
    have hle : pointIdeal x y ≤ RingHom.ker (planeEval x y) := by
      rw [pointIdeal, Ideal.span_le]
      rintro _ (rfl | rfl) <;> simp
    exact hle hP
  · intro hP
    have key : ∀ Q : BPoly, Q - C (planeEval x y Q) ∈ pointIdeal x y := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          simpa [map_add, C_add, add_sub_add_comm] using Ideal.add_mem _ hp hq
      | mul_X p i hp =>
          have hi : X i - C (planeEval x y (X i)) ∈ pointIdeal x y := by
            fin_cases i
            · exact Ideal.subset_span (by simp)
            · exact Ideal.subset_span (by simp)
          have he : p * X i - C (planeEval x y (p * X i)) =
              (p - C (planeEval x y p)) * X i +
                C (planeEval x y p) * (X i - C (planeEval x y (X i))) := by
            simp only [map_mul]
            ring
          rw [he]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hi)
    simpa [hP] using key P
end

#print axioms solution
