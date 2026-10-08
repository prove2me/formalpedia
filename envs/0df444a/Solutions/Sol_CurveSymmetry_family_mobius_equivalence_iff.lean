-- Prove2me | solution 1 for CurveSymmetry.family_mobius_equivalence_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:30.512877+00:00
-- url     : https://prove2.me/submissions/a4e02ca4-e6b7-4573-8114-f833ca0c93e6

-- Solution generated from lean/FamilySphereClassification.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_dilation_parameter
import Theorems.Thm_CurveSymmetry_family_inversion_parameter
import Theorems.Thm_CurveSymmetry_family_mobius_complete
import Theorems.Thm_CurveSymmetry_family_sphere_dilation_proportional
import Theorems.Thm_CurveSymmetry_family_sphere_inversion_proportional
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
theorem family_sphere_dilation_parameter {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m β) :
    ‖c‖ = 1 ∧ β = α := by
  obtain ⟨k, _, hk⟩ := family_sphere_dilation_proportional hm ha hb hc hmap
  exact family_dilation_parameter hm hα hβ hc hk
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
theorem family_sphere_inversion_parameter {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (ha : α ≠ star α) (hb : β ≠ star β)
    (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m β) :
    ‖c‖ = 1 ∧ β = α := by
  obtain ⟨k, _, he⟩ := family_sphere_inversion_proportional hm ha hb hc hmap
  exact family_inversion_parameter hm hα hβ hc he
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem family_mobius_parameter_necessary {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) : β = α := by
  obtain ⟨c, hc, he | he⟩ := family_mobius_complete hm ha hb g hmap
  · exact (family_sphere_dilation_parameter (by omega) ha hb hα hβ hc
      (fun p hp => (he p) ▸ hmap p hp)).2
  · exact (family_sphere_inversion_parameter (by omega) hα hβ ha hb hc
      (fun p hp => (he p) ▸ hmap p hp)).2
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    (∃ g : MobiusMatrix, (fun p : Sphere => g • p) '' sphericalFamily m α =
      sphericalFamily m β) ↔ β = α := by
  constructor
  · rintro ⟨g, hg⟩
    apply family_mobius_parameter_necessary hm ha hb hα hβ g
    intro p hp
    rw [← hg]
    exact ⟨p, hp, rfl⟩
  · rintro rfl
    exact ⟨1, by simp⟩
end

#print axioms solution
