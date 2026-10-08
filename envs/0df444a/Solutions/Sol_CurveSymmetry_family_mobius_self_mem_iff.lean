-- Prove2me | solution 1 for CurveSymmetry.family_mobius_self_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:53.861029+00:00
-- url     : https://prove2.me/submissions/212e0e93-a1e4-4c72-8e7b-01a643a92477

-- Solution generated from lean/FamilySphereClassification.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_mobius_self_filter
import Theorems.Thm_CurveSymmetry_family_sphere_dilation_filter
import Theorems.Thm_CurveSymmetry_family_sphere_inversion_filter
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
open MvPolynomial OnePoint
theorem family_sphere_dilation_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = 1) (p : Sphere) :
    sphereDilation c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · intro hp
    have hi : (c⁻¹) ^ (2 * m) = 1 := by rw [inv_pow, hroot, inv_one]
    have hback := (family_sphere_dilation_filter hm ha hα (inv_ne_zero hc)).mpr hi
      (sphereDilation c p) hp
    have he : sphereDilation c⁻¹ (sphereDilation c p) = p := by
      cases p using OnePoint.rec <;> simp [sphereDilation, hc]
    rwa [he] at hback
  · exact (family_sphere_dilation_filter hm ha hα hc).mpr hroot p
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
lemma sphereInversion_involutive {c : ℂ} (hc : c ≠ 0) :
    Function.Involutive (sphereInversion c) := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInversion]
  | coe z =>
    by_cases hz : z = 0
    · simp [sphereInversion, hz]
    · simp only [sphereInversion, OnePoint.elim_some, if_neg hz,
        if_neg (div_ne_zero hc hz), OnePoint.coe_eq_coe]
      field_simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
/-- The root condition preserves membership in both directions on the whole
sphere, since inversion exchanges zero and infinity and is an involution. -/
theorem family_sphere_inversion_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = star α ^ 2) (p : Sphere) :
    sphereInversion c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  have hmap := (family_sphere_inversion_filter hm hα ha hc).mpr hroot
  constructor
  · intro hp
    simpa only [sphereInversion_involutive hc p] using hmap (sphereInversion c p) hp
  · exact hmap p
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) (p : Sphere) :
    g • p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := (family_mobius_self_filter hm ha hα g).mp hmap
  · rw [he]
    exact family_sphere_dilation_mem_iff (by omega) ha hα hc hr p
  · rw [he]
    exact family_sphere_inversion_mem_iff (by omega) hα ha hc hr p
end

#print axioms solution
