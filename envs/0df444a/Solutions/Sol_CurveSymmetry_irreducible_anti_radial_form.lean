-- Prove2me | solution 1 for CurveSymmetry.irreducible_anti_radial_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:20.867746+00:00
-- url     : https://prove2.me/submissions/4b0c296c-346a-4a5c-a01e-568e056328cb

-- Solution generated from lean/RadialAntiForm.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Theorems.Thm_CurveSymmetry_anti_radial_form
import Theorems.Thm_CurveSymmetry_not_irreducible_pure_powers
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma weightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (weightPolynomial P m).coeff k = P.coeff (exponent (k + m) k) := by
  classical
  simp only [weightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent (k + m) k, mem_support_iff.mpr (Ne.symm hc), by simp⟩)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma oppositeWeightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (oppositeWeightPolynomial P m).coeff k = P.coeff (exponent k (k + m)) := by
  classical
  simp only [oppositeWeightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent k (k + m), mem_support_iff.mpr (Ne.symm hc), by simp⟩)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma oppositeWeightPolynomial_eq_map {P : BPoly} (m : ℕ)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    oppositeWeightPolynomial P m = (weightPolynomial P m).map (starRingEnd ℂ) := by
  ext k
  rw [oppositeWeightPolynomial_coeff, Polynomial.coeff_map, weightPolynomial_coeff, hreal]
  rfl
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly} (hirr : Irreducible P)
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ A : Polynomial ℂ,
      P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
        (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
      1 ≤ A.natDegree ∧ A.natDegree ≤ (P.totalDegree - m) / 2 ∧ m + 2 ≤ P.totalDegree := by
  obtain ⟨hform, hA, -⟩ := anti_radial_form (by omega) hζ hdeg hanti
  rw [oppositeWeightPolynomial_eq_map m hreal] at hform
  have h1 : 1 ≤ (weightPolynomial P m).natDegree := by
    by_contra h0
    have hAC := Polynomial.eq_C_of_natDegree_eq_zero (by omega :
      (weightPolynomial P m).natDegree = 0)
    rw [hAC, Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq] at hform
    apply not_irreducible_pure_powers m hm ((weightPolynomial P m).coeff 0)
      (starRingEnd ℂ ((weightPolynomial P m).coeff 0))
    convert hirr using 1
    conv_rhs => rw [hform]
    ring
  exact ⟨weightPolynomial P m, hform, h1, hA, by omega⟩
end

#print axioms solution
