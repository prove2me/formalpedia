-- Prove2me | solution 1 for CurveSymmetry.fourTermForm_tangent_data
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:03.963993+00:00
-- url     : https://prove2.me/submissions/24c8bdb4-2bad-4562-933a-6e6f299b2550

-- Solution generated from lean/FamilyCharts.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma binaryForm_homogeneous (m : ℕ) (a b : ℂ) : (binaryForm m a b).IsHomogeneous m :=
  (isHomogeneous_C_mul_X_pow a 0 m).add (isHomogeneous_C_mul_X_pow b 1 m)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_components (m n : ℕ) (a b c d : ℂ) :
    homogeneousComponent n (fourTermForm m a b c d) =
      (if n = m then binaryForm m a b else 0) +
        (if n = m + 2 then X 0 * X 1 * binaryForm m c d else 0) := by
  have hhigh : (X 0 * X 1 * binaryForm m c d).IsHomogeneous (m + 2) := by
    convert ((isHomogeneous_X ℂ (0 : Fin 2)).mul (isHomogeneous_X ℂ 1)).mul
      (binaryForm_homogeneous m c d) using 1
    omega
  rw [fourTermForm, map_add, homogeneousComponent_of_mem (binaryForm_homogeneous m a b),
    homogeneousComponent_of_mem hhigh]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (c d : ℂ) :
    (∀ n < m, homogeneousComponent n (fourTermForm m a b c d) = 0) ∧
      homogeneousComponent m (fourTermForm m a b c d) = binaryForm m a b ∧
      binaryForm m a b ≠ 0 ∧
      Polynomial.Separable (Polynomial.C a * Polynomial.X ^ m + Polynomial.C b) := by
  refine ⟨?_, ?_, ?_, binary_tangent_separable hm ha hb⟩
  · intro n hn
    rw [fourTermForm_components, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [fourTermForm_components, if_pos rfl, if_neg (by omega), add_zero]
  · intro hz
    have he := congrArg (planeEval 1 0) hz
    simp [binaryForm, hm.ne'] at he
    exact ha he
end

#print axioms solution
