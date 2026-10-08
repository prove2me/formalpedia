-- Prove2me | solution 1 for CurveSymmetry.fourTermForm_singular_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:02.953631+00:00
-- url     : https://prove2.me/submissions/820e72c5-4950-4525-beaa-046564127d3d

-- Solution generated from lean/FamilySingularities.lean (curve-symmetry-lean): inlined helpers in
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
lemma binaryForm_euler (m : ℕ) (a b : ℂ) :
    X 0 * pderiv 0 (binaryForm m a b) + X 1 * pderiv 1 (binaryForm m a b) =
      (m : BPoly) * binaryForm m a b := by
  cases m with
  | zero => simp [binaryForm]
  | succ n =>
      simp only [binaryForm, map_add, pderiv_C_mul, pderiv_pow]
      simp [pow_succ]
      ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_euler (m : ℕ) (a b c d : ℂ) :
    X 0 * pderiv 0 (fourTermForm m a b c d) +
      X 1 * pderiv 1 (fourTermForm m a b c d) =
      (m : BPoly) * fourTermForm m a b c d + 2 * X 0 * X 1 * binaryForm m c d := by
  have hlow := binaryForm_euler m a b
  have hhigh := binaryForm_euler m c d
  simp only [fourTermForm, map_add, pderiv_mul, pderiv_X, Pi.single_apply, Fin.isValue,
    show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, zero_mul,
    mul_zero, one_mul, mul_one, zero_add, add_zero]
  linear_combination hlow + (X 0 : BPoly) * X 1 * hhigh
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_eval (m : ℕ) (a b c d x y : ℂ) :
    planeEval x y (fourTermForm m a b c d) =
      a * x ^ m + b * y ^ m + x * y * (c * x ^ m + d * y ^ m) := by
  simp [fourTermForm, binaryForm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_not_singular_on_torus {m : ℕ} {a b c d x y : ℂ}
    (hdet : a * d - b * c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ¬ JacobianSingular (fourTermForm m a b c d) x y := by
  rintro ⟨hp, hpx, hpy⟩
  have he := congrArg (planeEval x y) (fourTermForm_euler m a b c d)
  simp only [map_add, map_mul, planeEval_X_zero, planeEval_X_one, hpx, hpy, hp,
    mul_zero, zero_add, map_ofNat, binaryForm, map_pow, planeEval_C] at he
  have hv : c * x ^ m + d * y ^ m = 0 := by
    apply (mul_eq_zero.mp he.symm).resolve_left
    exact mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  rw [fourTermForm_eval, hv, mul_zero, add_zero] at hp
  have hz : (a * d - b * c) * x ^ m = 0 := by linear_combination d * hp - b * hv
  exact (mul_ne_zero hdet (pow_ne_zero m hx)) hz
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_origin_singular {m : ℕ} (hm : 2 ≤ m) (a b c d : ℂ) :
    JacobianSingular (fourTermForm m a b c d) 0 0 := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  simp [JacobianSingular, fourTermForm, binaryForm, hm0, hm1]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 2 ≤ m) {a b c d x y : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hdet : a * d - b * c ≠ 0) :
    JacobianSingular (fourTermForm m a b c d) x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hs
    have hp := hs.1
    rw [fourTermForm_eval] at hp
    by_cases hx : x = 0
    · refine ⟨hx, ?_⟩
      simp only [hx, zero_pow (by omega : m ≠ 0), mul_zero, zero_mul, zero_add, add_zero] at hp
      exact (pow_eq_zero_iff (by omega : m ≠ 0)).mp ((mul_eq_zero.mp hp).resolve_left hb)
    · by_cases hy : y = 0
      · simp only [hy, zero_pow (by omega : m ≠ 0), mul_zero, zero_mul, add_zero] at hp
        exact ((mul_ne_zero ha (pow_ne_zero m hx)) hp).elim
      · exact (fourTermForm_not_singular_on_torus hdet hx hy hs).elim
  · rintro ⟨rfl, rfl⟩
    exact fourTermForm_origin_singular hm a b c d
end

#print axioms solution
