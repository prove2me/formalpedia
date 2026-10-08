-- Prove2me | solution 1 for CurveSymmetry.no_translation_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:40.512978+00:00
-- url     : https://prove2.me/submissions/8c06ada0-61b6-4429-ab76-0f2c9ff4d5af

-- Solution generated from lean/Translation.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Theorems.Thm_CurveSymmetry_lineEquation_degree
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A nonunit divisor of an irreducible polynomial has the same degree. -/
lemma degree_le_of_nonunit_dvd {P L : BPoly} (hP : Irreducible P)
    (hL : ¬ IsUnit L) (hdiv : L ∣ P) : P.totalDegree ≤ L.totalDegree := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hunit : IsUnit Q := (hP.isUnit_or_isUnit hQ).resolve_left hL
  have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rw [hQ]
  simpa [hzero] using totalDegree_mul L Q
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_lineRestriction (P : BPoly) (z v t : ℂ) :
    (lineRestriction z v P).eval t =
      eval (fun i : Fin 2 => if i = 0 then z + v * t else star z + star v * t) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineRestriction]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, Polynomial.eval_mul, hP]
      fin_cases i <;> simp [lineRestriction]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_lineEquation (z v w : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then w else star w) (lineEquation z v) =
      star v * w - v * star w - (star v * z - v * star z) := by
  simp [lineEquation]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma lineEquation_irreducible (z v : ℂ) (hv : v ≠ 0) : Irreducible (lineEquation z v) := by
  have hd := lineEquation_degree z v hv
  apply irreducible_of_totalDegree_eq_one hd
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hzero : lineEquation z v = 0 := by
    ext s
    have h := ha s
    simpa [hz] using h
  simp [hzero] at hd
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma lineEquation_realLocus_infinite (z v : ℂ) (hv : v ≠ 0) :
    (realLocus (lineEquation z v)).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => z + v * (n : ℂ)) := by
    intro n m h
    have hnm : (n : ℂ) = m := mul_left_cancel₀ hv (add_left_cancel h)
    exact_mod_cast hnm
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  change eval _ (lineEquation z v) = 0
  rw [eval_lineEquation]
  simp only [star_add, star_mul, star_natCast]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {v : ℂ}
    (htrans : ∀ z ∈ realLocus P, z + v ∈ realLocus P) : v = 0 := by
  by_contra hv
  obtain ⟨z, hz⟩ := hne
  have horbit : ∀ n : ℕ, z + v * (n : ℂ) ∈ realLocus P := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        convert htrans (z + v * (n : ℂ)) ih using 1
        push_cast
        ring
  have hrestriction : lineRestriction z v P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hninj : Function.Injective (fun n : ℕ => (n : ℂ)) := Nat.cast_injective
    apply (Set.infinite_range_of_injective hninj).mono
    rintro _ ⟨n, rfl⟩
    change (lineRestriction z v P).eval (n : ℂ) = 0
    rw [eval_lineRestriction]
    have h := horbit n
    simpa only [realLocus, Set.mem_ofPred_eq, star_add, star_mul, star_natCast, mul_comm] using h
  have hsub : realLocus (lineEquation z v) ⊆ realLocus P := by
    intro w hw
    change eval _ (lineEquation z v) = 0 at hw
    rw [eval_lineEquation] at hw
    have hx : z + v * ((w - z) / v) = w := by field_simp; ring
    have hy : star z + star v * ((w - z) / v) = star w := by
      field_simp
      linear_combination hw
    have he := eval_lineRestriction P z v ((w - z) / v)
    rw [hrestriction, Polynomial.eval_zero, hx, hy] at he
    exact he.symm
  have hL := lineEquation_irreducible z v hv
  have hdiv := dvd_of_realLocus_subset hL (lineEquation_realLocus_infinite z v hv) hsub
  have hb := degree_le_of_nonunit_dvd hP hL.not_isUnit hdiv
  rw [lineEquation_degree z v hv] at hb
  omega
end

#print axioms solution
