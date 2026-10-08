-- Prove2me | solution 1 for CurveSymmetry.family_mobius_self_filter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:31.385493+00:00
-- url     : https://prove2.me/submissions/fbb84a61-642f-41c5-adba-88c3fe836460

-- Solution generated from lean/FamilySphereClassification.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_mobius_complete
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

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix) :
    (∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) ↔
      ∃ c : ℂ, c ≠ 0 ∧
        ((c ^ (2 * m) = 1 ∧ ∀ p : Sphere, g • p = sphereDilation c p) ∨
         (c ^ (2 * m) = star α ^ 2 ∧ ∀ p : Sphere, g • p = sphereInversion c p)) := by
  have hm0 : 0 < m := by omega
  constructor
  · intro hmap
    obtain ⟨c, hc, he | he⟩ := family_mobius_complete hm ha ha g hmap
    · exact ⟨c, hc, Or.inl ⟨(family_sphere_dilation_filter hm0 ha hα hc).mp
        (fun p hp => (he p) ▸ hmap p hp), he⟩⟩
    · exact ⟨c, hc, Or.inr ⟨(family_sphere_inversion_filter hm0 hα ha hc).mp
        (fun p hp => (he p) ▸ hmap p hp), he⟩⟩
  · rintro ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ p hp
    · rw [he]
      exact (family_sphere_dilation_filter hm0 ha hα hc).mpr hr p hp
    · rw [he]
      exact (family_sphere_inversion_filter hm0 hα ha hc).mpr hr p hp
end

#print axioms solution
