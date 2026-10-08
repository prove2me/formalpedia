-- Prove2me | solution 1 for CurveSymmetry.irreducible_radial_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:07.682577+00:00
-- url     : https://prove2.me/submissions/169f7285-9262-4429-b8bf-13b5c32f6ab2

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
/-- Diagonal monomial support is exactly a polynomial in `XY`. -/
lemma radial_representation {P : BPoly}
    (hdiag : ∀ s ∈ P.support, s 0 = s 1) :
    ∃ Q : Polynomial ℂ, P = Polynomial.aeval ((X 0 : BPoly) * X 1) Q := by
  classical
  refine ⟨∑ s ∈ P.support, Polynomial.monomial (s 0) (P.coeff s), ?_⟩
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he : s = exponent (s 0) (s 0) := exponent_eq_iff.mpr ⟨rfl, (hdiag s hs).symm⟩
  rw [Polynomial.aeval_monomial, he, monomial_exponent]
  simp [mul_pow, mul_assoc]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma radial_factor_not_isUnit (r : ℂ) : ¬ IsUnit ((X 0 : BPoly) * X 1 - C r) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then r else 1))
  simp at h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hirr : Irreducible P)
    (hdiag : ∀ s ∈ P.support, s 0 = s 1) :
    ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r) := by
  obtain ⟨Q, hQ⟩ := radial_representation hdiag
  have hdegree : Q.degree ≠ 0 := by
    intro hd
    have hnat : Q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnat, Polynomial.aeval_C] at hQ
    have hc : Q.coeff 0 ≠ 0 := by
      intro hzero
      apply hirr.ne_zero
      simpa [hzero] using hQ
    apply hirr.not_isUnit
    rw [hQ]
    exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ BPoly)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q hdegree
  have hdiv : ((X 0 : BPoly) * X 1 - C r) ∣ P := by
    rw [hQ]
    have hroot : (Polynomial.X - Polynomial.C r : Polynomial ℂ) ∣ Q :=
      Polynomial.dvd_iff_isRoot.mpr hr
    have hmap := Polynomial.aeval_dvd ((X 0 : BPoly) * X 1) hroot
    convert hmap using 1
    simp [Polynomial.aeval_def]
  obtain ⟨S, hS⟩ := hdiv
  have hu : IsUnit S := (hirr.isUnit_or_isUnit hS).resolve_left (radial_factor_not_isUnit r)
  obtain ⟨a, ha, hSa⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  refine ⟨a, r, isUnit_iff_ne_zero.mp ha, ?_⟩
  rw [hS, hSa, mul_comm]
end

#print axioms solution
