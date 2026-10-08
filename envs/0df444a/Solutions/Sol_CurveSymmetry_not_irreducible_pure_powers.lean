-- Prove2me | solution 1 for CurveSymmetry.not_irreducible_pure_powers
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:17.321654+00:00
-- url     : https://prove2.me/submissions/8df25cf4-ec9c-4a7e-be4b-da7ceb5b1cf7

-- Solution generated from lean/Irreducibility.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
lemma linear_not_isUnit (c : ℂ) : ¬ IsUnit ((X 0 : BPoly) - C c * X 1) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => 0))
  simp at h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (m : ℕ) (hm : 2 ≤ m) (a b : ℂ) :
    ¬ Irreducible (C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m) := by
  intro hirr
  have hhom : (C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m).IsHomogeneous m :=
    (isHomogeneous_X_pow 0 m).C_mul a |>.add ((isHomogeneous_X_pow 1 m).C_mul b)
  have hdegree := hhom.totalDegree hirr.ne_zero
  by_cases ha : a = 0
  · have hY : ¬ IsUnit (X 1 : BPoly) := by
      intro hu
      have := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
      simp at this
    have hdiv : (X 1 : BPoly) ∣ C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m := by
      simp only [ha, map_zero, zero_mul, zero_add]
      exact dvd_mul_of_dvd_right (dvd_pow_self (X 1) (by omega)) (C b)
    have h := degree_le_of_nonunit_dvd hirr hY hdiv
    simp only [totalDegree_X, hdegree] at h
    omega
  · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) (by omega : 0 < m)
    have hab : a * c ^ m = -b := by rw [hc]; field_simp
    have hform : C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m =
        C a * ((X 0 : BPoly) ^ m - (C c * X 1) ^ m) := by
      rw [mul_pow, ← map_pow C]
      have hab' : (C a : BPoly) * C (c ^ m) = -C b := by rw [← map_mul, hab, map_neg]
      linear_combination hab' * (X 1 : BPoly) ^ m
    have hdiv : ((X 0 : BPoly) - C c * X 1) ∣
        C a * (X 0 : BPoly) ^ m + C b * X 1 ^ m := by
      rw [hform]
      exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ m) (C a)
    have h := (degree_le_of_nonunit_dvd hirr (linear_not_isUnit c) hdiv).trans
      (linear_degree_le c)
    omega
end

#print axioms solution
