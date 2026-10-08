-- Prove2me | solution 1 for CurveSymmetry.family_direct_card
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:29.564125+00:00
-- url     : https://prove2.me/submissions/232eb648-6531-46ba-8e09-4a003003b27a

-- Solution generated from lean/FamilyRotations.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_direct_euclidean_bound
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_family_root_symmetry
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
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    Nat.card (DirectSymmetries (familyPolynomial m α)) = 2 * m := by
  have hm' : 0 < m := by omega
  obtain ⟨hf, hb⟩ := direct_euclidean_bound (familyPolynomial_irreducible hm' ha)
    (by rw [family_degree hm']; omega) (family_realLocus_infinite hm' ha) (family_not_circle hm' ha)
  let := hf
  let : NeZero (2 * m) := ⟨by omega⟩
  let f : rootsOfUnity (2 * m) ℂ → DirectSymmetries (familyPolynomial m α) := fun u =>
    ⟨((u.val : ℂ), 0), family_root_symmetry hm' ((mem_rootsOfUnity' _ _).mp u.prop) α⟩
  have hi : Function.Injective f := by
    intro u v h
    exact rootsOfUnity.coe_injective (congrArg (fun w => w.val.1) h)
  have hlo := Nat.card_le_card_of_injective f hi
  rw [Complex.card_rootsOfUnity] at hlo
  rw [family_degree hm'] at hb
  omega
end

#print axioms solution
