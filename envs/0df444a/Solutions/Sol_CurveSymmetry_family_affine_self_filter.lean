-- Prove2me | solution 1 for CurveSymmetry.family_affine_self_filter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:50.194981+00:00
-- url     : https://prove2.me/submissions/7c1d6eab-a365-4774-a35b-3d3ce895d347

-- Solution generated from lean/FamilyEuclidean.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_mobius_self_filter
import Theorems.Thm_CurveSymmetry_sphericalFamily_eq
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
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_finite_formula (g : MobiusMatrix) (z : ℂ) :
    g • (z : Sphere) = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_infinity_formula (g : MobiusMatrix) :
    g • (∞ : Sphere) = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g
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
noncomputable section
theorem affineMobiusMatrix_finite (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineMobiusMatrix a b ha • (z : Sphere) = ((a * z + b : ℂ) : Sphere) := by
  simp [mobius_finite_formula, affineMobiusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem affineMobiusMatrix_infinity (a b : ℂ) (ha : a ≠ 0) :
    affineMobiusMatrix a b ha • (∞ : Sphere) = ∞ := by
  simp [mobius_infinity_formula, affineMobiusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α a b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (ha0 : a ≠ 0)
    (hf : ∀ z ∈ extremalCurve m α, a * z + b ∈ extremalCurve m α) :
    b = 0 ∧ a ^ (2 * m) = 1 := by
  have hs : ∀ p ∈ sphericalFamily m α,
      affineMobiusMatrix a b ha0 • p ∈ sphericalFamily m α := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => simpa [affineMobiusMatrix_infinity] using
        infinity_mem_sphericalFamily (by omega : 0 < m) ha
    | coe z =>
      simpa [affineMobiusMatrix_finite] using
        (finite_mem_sphericalFamily_iff (by omega) ha (a * z + b)).mpr
          (hf z ((finite_mem_sphericalFamily_iff (by omega) ha z).mp hp))
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ :=
    (family_mobius_self_filter hm ha hα (affineMobiusMatrix a b ha0)).mp hs
  · have h0 := he ((0 : ℂ) : Sphere)
    have h1 := he ((1 : ℂ) : Sphere)
    have hb : b = 0 := by simpa [affineMobiusMatrix_finite, sphereDilation] using h0
    have hac : a = c := by simpa [affineMobiusMatrix_finite, sphereDilation, hb] using h1
    exact ⟨hb, hac ▸ hr⟩
  · have hi := he ∞
    simp [affineMobiusMatrix_infinity, sphereInversion] at hi
end

#print axioms solution
