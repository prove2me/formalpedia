-- Prove2me | solution 1 for CurveSymmetry.sphericalFamily_projective_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:28.45363+00:00
-- url     : https://prove2.me/submissions/e5478c83-1d93-4b61-854c-0336b62b85f4

-- Solution generated from lean/FamilyProjective.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_sphericalFamily_eq
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
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma sphereProjectiveEquiv_finite (z : ℂ) :
    sphereProjectiveEquiv (z : Sphere) = Projectivization.mk ℂ ![z, 1] (by simp) := rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma sphereProjectiveEquiv_infinity :
    sphereProjectiveEquiv (∞ : Sphere) = Projectivization.mk ℂ ![1, 0] (by simp) := rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem finite_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    (z : Sphere) ∈ sphericalFamily m α ↔ z ∈ extremalCurve m α := by
  rw [sphericalFamily_eq hm ha]
  simp only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
    Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem infinity_mem_sphericalFamily {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : (∞ : Sphere) ∈ sphericalFamily m α := by
  rw [sphericalFamily_eq hm ha]
  exact Set.mem_insert _ _
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_smul_left (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α (a • x) y = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_smul_right (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α x (a • y) = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem familyProjective_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ familyProjectiveCurve m α ↔
      familyBihomogeneous m α x y = 0 := by
  change familyBihomogeneous m α (Projectivization.mk ℂ x hx).rep
    (Projectivization.mk ℂ y hy).rep = 0 ↔ _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  simp [Units.smul_def, familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_affine (m : ℕ) (α x y : ℂ) :
    familyBihomogeneous m α ![x, 1] ![y, 1] = planeEval x y (familyPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem familyProjective_affine_iff (m : ℕ) (α x y : ℂ) :
    (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m α ↔ planeEval x y (familyPolynomial m α) = 0 := by
  rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite, familyProjective_mk_iff,
    familyBihomogeneous_affine]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyProjective_infinity_infinity {m : ℕ} (hm : 0 < m) (α : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∈
      familyProjectiveCurve m α := by
  rw [sphereProjectiveEquiv_infinity, familyProjective_mk_iff]
  simp [familyBihomogeneous, hm.ne']
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    sphereRealDiagonal p ∈ familyProjectiveCurve m α ↔ p ∈ sphericalFamily m α := by
  cases p using OnePoint.rec with
  | infty =>
    change (sphereProjectiveEquiv ∞, sphereProjectiveEquiv ∞) ∈ familyProjectiveCurve m α ↔ _
    exact iff_of_true (familyProjective_infinity_infinity hm α) (infinity_mem_sphericalFamily hm ha)
  | coe z =>
    change (sphereProjectiveEquiv (z : Sphere), sphereProjectiveEquiv ((star z : ℂ) : Sphere)) ∈
      familyProjectiveCurve m α ↔ _
    rw [familyProjective_affine_iff, finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
    rfl
end

#print axioms solution
