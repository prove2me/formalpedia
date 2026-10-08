-- Prove2me | solution 1 for CurveSymmetry.family_no_opposite
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:55.527911+00:00
-- url     : https://prove2.me/submissions/0c783994-e163-4146-8c9c-571b7da29450

-- Solution generated from lean/FamilyRotations.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_direct_bound_with_opposite
import Theorems.Thm_CurveSymmetry_family_direct_card
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
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
theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_not_circle {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    NotCircle (familyPolynomial m α) := by
  rintro ⟨c, R, hR, he⟩
  obtain ⟨z, hz, hn⟩ := family_point_of_norm hm ha
    (show 0 ≤ ‖c‖ + R + 1 by positivity)
  rw [he, Metric.mem_sphere, dist_eq_norm] at hz
  have hb := norm_add_le (z - c) c
  rw [sub_add_cancel, hz, hn] at hb
  linarith
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    IsEmpty (OppositeSymmetries (familyPolynomial m α)) := by
  refine ⟨fun g => ?_⟩
  have hm' : 0 < m := by omega
  have hb := direct_bound_with_opposite (familyPolynomial_irreducible hm' ha)
    (by rw [family_degree hm']; omega) (family_realLocus_infinite hm' ha)
    (family_not_circle hm' ha) g
  rw [family_direct_card (by omega) ha, family_degree hm'] at hb
  omega
end

#print axioms solution
