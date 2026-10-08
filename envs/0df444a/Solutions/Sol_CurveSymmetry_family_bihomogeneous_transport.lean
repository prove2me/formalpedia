-- Prove2me | solution 1 for CurveSymmetry.family_bihomogeneous_transport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:37.582702+00:00
-- url     : https://prove2.me/submissions/27b37a03-6ec2-432d-86c5-4141b14b4fca

-- Solution generated from lean/FamilyGlobalTransport.lean (curve-symmetry-lean): inlined helpers in
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
lemma familyBihomogeneous_affine (m : ℕ) (α x y : ℂ) :
    familyBihomogeneous m α ![x, 1] ![y, 1] = planeEval x y (familyPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma familyMobiusPullback_eval (m : ℕ) (β x y : ℂ) (g : MobiusMatrix) :
    planeEval x y (familyMobiusPullback m β g) =
      familyBihomogeneous m β (g • ![x, 1]) ((g.map (starRingEnd ℂ)) • ![y, 1]) := by
  simp [familyMobiusPullback, mobiusX, mobiusY, familyBihomogeneous,
    Matrix.GeneralLinearGroup.fin_two_smul]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma normalize_homogeneous_pair (a b : ℂ) (hb : b ≠ 0) :
    ![a, b] = b • (![a / b, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  field_simp
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (he : familyMobiusPullback m β g = C k * familyPolynomial m α)
    (x y : Fin 2 → ℂ) :
    familyBihomogeneous m β (g • x) ((g.map (starRingEnd ℂ)) • y) =
      k * familyBihomogeneous m α x y := by
  have haffine (u v : ℂ) :
      familyBihomogeneous m β (g • ![u, 1]) ((g.map (starRingEnd ℂ)) • ![v, 1]) =
        k * familyBihomogeneous m α ![u, 1] ![v, 1] := by
    rw [← familyMobiusPullback_eval, he, map_mul, planeEval_C, familyBihomogeneous_affine]
  let F : ℂ × ℂ → ℂ := fun st =>
    familyBihomogeneous m β (g • ![x 0, st.1]) ((g.map (starRingEnd ℂ)) • ![y 0, st.2])
  let G : ℂ × ℂ → ℂ := fun st => k * familyBihomogeneous m α ![x 0, st.1] ![y 0, st.2]
  have hF : Continuous F := by
    dsimp [F]
    simp only [Matrix.GeneralLinearGroup.fin_two_smul]
    unfold familyBihomogeneous
    fun_prop
  have hG : Continuous G := by
    dsimp [G, familyBihomogeneous]
    fun_prop
  have hdense : Dense (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
    (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))
  have hFG : F = G := by
    apply Continuous.ext_on hdense hF hG
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs0 : s ≠ 0 := hs
    have ht0 : t ≠ 0 := ht
    dsimp [F, G]
    rw [normalize_homogeneous_pair (x 0) s hs0, normalize_homogeneous_pair (y 0) t ht0,
      smul_comm g s, smul_comm (g.map (starRingEnd ℂ)) t]
    simp only [familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
    rw [haffine]
    ring
  have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have hy : ![y 0, y 1] = y := by ext i; fin_cases i <;> rfl
  have h := congrFun hFG (x 1, y 1)
  dsimp [F, G] at h
  simpa only [hx, hy] using h
end

#print axioms solution
