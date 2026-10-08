-- Prove2me | solution 1 for CurveSymmetry.reciprocal_affine_points_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:26.717983+00:00
-- url     : https://prove2.me/submissions/7c8fb5d3-1832-40f4-96de-5c29eb80308d

-- Solution generated from lean/AffineChartImages.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_reciprocal_chart_complex_closure
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
/-- Clearing the two inversion denominators gives the reciprocal chart equation. -/
lemma family_reciprocal_chart (m : ℕ) (α : ℂ) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v) ^ (m + 1) * planeEval u⁻¹ v⁻¹ (familyPolynomial m α) =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval, familyInfinityPolynomial, fourTermForm_eval]
  simp only [mul_pow, pow_succ, inv_pow, one_mul]
  field_simp
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma vector_eta (z : Fin 2 → ℂ) : ![z 0, z 1] = z := by
  ext i
  fin_cases i <;> rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma planeEval_vector (x y : ℂ) : planeEval x y = eval ![x, y] := by
  unfold planeEval
  congr 1
  funext i
  fin_cases i <;> rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma reciprocal_vector_zero_iff (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    eval w (familyInfinityPolynomial m α) = 0 ↔
      eval ![(w 0)⁻¹, (w 1)⁻¹] (familyPolynomial m α) = 0 := by
  have h := family_reciprocal_chart m α h0 h1
  rw [planeEval_vector, planeEval_vector, vector_eta] at h
  rw [← h, mul_eq_zero]
  simp [pow_ne_zero _ (mul_ne_zero h0 h1)]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Simultaneous inversion identifies original affine points off both axes
with the reciprocal chart off both axes. No zero denominator is included. -/
theorem reciprocal_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 0)⁻¹, (z 1)⁻¹]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0 ∧ z 1 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyInfinityPolynomial m α) = 0 ∧
        w 0 ≠ 0 ∧ w 1 ≠ 0} := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, h0, h1⟩, rfl⟩
    refine ⟨(reciprocal_vector_zero_iff m α _ (inv_ne_zero h0)
      (inv_ne_zero h1)).mpr ?_, inv_ne_zero h0, inv_ne_zero h1⟩
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      inv_inv, vector_eta] using hz
  · rintro w ⟨hw, h0, h1⟩
    refine ⟨![(w 0)⁻¹, (w 1)⁻¹],
      ⟨(reciprocal_vector_zero_iff m α w h0 h1).mp hw,
        inv_ne_zero h0, inv_ne_zero h1⟩, ?_⟩
    simpa using vector_eta w
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 0)⁻¹, (z 1)⁻¹]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0 ∧ z 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by
  have he := congrArg (Set.image affineSpectrumPoint) (reciprocal_affine_points_image m α)
  rw [Set.image_image] at he
  rw [he]
  exact reciprocal_chart_complex_closure hm α
end

#print axioms solution
