-- Prove2me | solution 1 for CurveSymmetry.sphericalFamily_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:55.484696+00:00
-- url     : https://prove2.me/submissions/82e31c9d-d798-44d4-a702-b5cefbe209c4

-- Solution generated from lean/SphereGeometry.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma extremalCurve_isClosed (m : ℕ) (α : ℂ) : IsClosed (extremalCurve m α) := by
  apply isClosed_eq _ continuous_const
  fun_prop
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma extremalCurve_not_isCompact {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    ¬ IsCompact (extremalCurve m α) := by
  intro hc
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨z, hz, hn⟩ := family_point_of_norm hm ha
    (show 0 ≤ max R 0 + 1 by positivity)
  rw [family_locus_eq] at hz
  have hb := hR z hz
  rw [hn] at hb
  have hmax := le_max_left R 0
  linarith
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
/-- A closed noncompact plane set gains exactly infinity under spherical closure. -/
lemma closure_onePoint_image {S : Set ℂ} (hs : IsClosed S) (hnc : ¬ IsCompact S) :
    closure (((↑) : ℂ → Sphere) '' S) = insert ∞ (((↑) : ℂ → Sphere) '' S) := by
  have hclosed : IsClosed (insert ∞ (((↑) : ℂ → Sphere) '' S)) := by
    apply (OnePoint.isClosed_iff_of_mem (Set.mem_insert _ _)).mpr
    convert hs using 1
    ext z
    simp
  have hsub := closure_minimal (Set.subset_insert ∞ (((↑) : ℂ → Sphere) '' S)) hclosed
  have hinf : ∞ ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    by_contra h
    have he : closure (((↑) : ℂ → Sphere) '' S) = ((↑) : ℂ → Sphere) '' S := by
      apply Set.Subset.antisymm _ subset_closure
      intro p hp
      rcases Set.mem_insert_iff.mp (hsub hp) with rfl | hp'
      · exact (h hp).elim
      · exact hp'
    exact hnc (OnePoint.isClosed_image_coe.mp (he ▸ isClosed_closure)).2
  exact Set.Subset.antisymm hsub (Set.insert_subset hinf subset_closure)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    sphericalFamily m α = insert ∞ (((↑) : ℂ → Sphere) '' extremalCurve m α) :=
  closure_onePoint_image (extremalCurve_isClosed m α) (extremalCurve_not_isCompact hm ha)
end

#print axioms solution
