-- Prove2me | solution 1 for CurveSymmetry.other_mixed_affine_points_image
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:18.713319+00:00
-- url     : https://prove2.me/submissions/0c6d483a-934c-4939-b8df-9e97dde4fc5c

-- Solution generated from lean/OtherMixedCornerClosure.lean (curve-symmetry-lean): inlined helpers in
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
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
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
open MvPolynomial
/-- The other mixed chart, written in coordinates `v=1/Y` and `X`. -/
lemma family_other_mixed_chart (m : ℕ) (α : ℂ) {x v : ℂ} (hv : v ≠ 0) :
    v ^ (m + 1) * planeEval x v⁻¹ (familyPolynomial m α) =
      planeEval v x (familyMixedPolynomial m (star α) α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyMixedPolynomial, map_add, map_mul, map_pow, planeEval_C,
    planeEval_X_zero, planeEval_X_one, pow_succ, inv_pow, one_mul]
  field_simp
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The second mixed chart uses the ordered coordinates `(1/Y, X)`.
Away from `Y = ∞` its equation is equivalent to the original affine equation. -/
lemma other_mixed_zero_iff (m : ℕ) (α : ℂ) {v x : ℂ} (hv : v ≠ 0) :
    planeEval v x (familyMixedPolynomial m (star α) α) = 0 ↔
      planeEval x v⁻¹ (familyPolynomial m α) = 0 := by
  rw [← family_other_mixed_chart m α hv, mul_eq_zero]
  simp [pow_ne_zero _ hv]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 1)⁻¹, z 0]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyMixedPolynomial m (star α) α) = 0 ∧
        w 0 ≠ 0} := by
  have he (z : Fin 2 → ℂ) : ![z 0, z 1] = z := by
    ext i
    fin_cases i <;> rfl
  have hep (x y : ℂ) : planeEval x y = eval ![x, y] := by
    unfold planeEval
    congr 1
    funext i
    fin_cases i <;> rfl
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, hy⟩, rfl⟩
    refine ⟨?_, inv_ne_zero hy⟩
    have h := (other_mixed_zero_iff m α (inv_ne_zero hy)).mpr
      (show planeEval (z 0) ((z 1)⁻¹)⁻¹ (familyPolynomial m α) = 0 by
        simpa only [inv_inv, hep, he] using hz)
    simpa only [hep] using h
  · rintro w ⟨hw, hv⟩
    refine ⟨![w 1, (w 0)⁻¹], ⟨?_, inv_ne_zero hv⟩, ?_⟩
    · have h := (other_mixed_zero_iff m α hv).mp
        (show planeEval (w 0) (w 1) (familyMixedPolynomial m (star α) α) = 0 by
          simpa only [hep, he] using hw)
      simpa only [hep] using h
    · simpa using he w
end

#print axioms solution
