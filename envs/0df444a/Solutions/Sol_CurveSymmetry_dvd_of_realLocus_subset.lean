-- Prove2me | solution 1 for CurveSymmetry.dvd_of_realLocus_subset
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:31.430773+00:00
-- url     : https://prove2.me/submissions/5df77f65-c7e9-4cb5-98c7-d4a31387883e

-- Solution generated from lean/Elimination.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
abbrev CoeffField := FractionRing UPoly
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma nestedEval_toNested (P : BPoly) (x y : ℂ) :
    nestedEval x y (toNested P) = eval (fun i : Fin 2 => if i = 0 then x else y) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [toNested_C, nestedEval]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [toNested_X_zero, toNested_X_one, nestedEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Clearing the two denominators in a Bézout identity over `ℂ(Y)[X]`. -/
lemma elimination_identity {P Q : NPoly} (hP : Irreducible P)
    (hdegree : P.natDegree ≠ 0) (hnot : ¬ P ∣ Q) :
    ∃ A B : NPoly, ∃ r : UPoly, r ≠ 0 ∧ A * P + B * Q = Polynomial.C r := by
  classical
  have : IsPrincipalIdealRing (Polynomial CoeffField) :=
    EuclideanDomain.to_principal_ideal_domain (R := Polynomial CoeffField)
  let f : UPoly →+* CoeffField := algebraMap UPoly CoeffField
  have hprim := hP.isPrimitive hdegree
  have hirr : Irreducible (P.map f) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := CoeffField)).mp hP
  have hcoprime : IsCoprime (P.map f) (Q.map f) := by
    rcases hirr.isCoprime_or_dvd (Q.map f) with h | h
    · exact h
    · exact (hnot (hprim.dvd_of_fraction_map_dvd_fraction_map h)).elim
  obtain ⟨A, B, hAB⟩ := hcoprime
  obtain ⟨b, hb, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors UPoly) A
  obtain ⟨d, hd, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors UPoly) B
  let A₀ := IsLocalization.integerNormalization (nonZeroDivisors UPoly) A
  let B₀ := IsLocalization.integerNormalization (nonZeroDivisors UPoly) B
  refine ⟨Polynomial.C d * A₀, Polynomial.C b * B₀, b * d,
    mul_ne_zero (nonZeroDivisors.ne_zero hb) (nonZeroDivisors.ne_zero hd), ?_⟩
  apply Polynomial.map_injective f (IsFractionRing.injective UPoly CoeffField)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  rw [hA, hB]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
  linear_combination Polynomial.C (f b) * Polynomial.C (f d) * hAB
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma infinite_conjugate_image {S : Set ℂ} (hS : S.Infinite) :
    (star '' S).Infinite := hS.image star_injective.injOn
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A nonzero equation with an infinite real locus cannot depend only on `Y`. -/
lemma nested_degree_ne_zero {P : BPoly} (hP : P ≠ 0)
    (hinf : (realLocus P).Infinite) : (toNested P).natDegree ≠ 0 := by
  intro hdegree
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  let r : UPoly := (toNested P).coeff 0
  have hr : r ≠ 0 := by
    intro hr
    have hz : toNested P = 0 := by simpa [r, hr] using hC
    exact hP (toNested.injective (by simpa using hz))
  apply infinite_conjugate_image hinf
  apply (Polynomial.finite_setOfPred_isRoot hr).subset
  rintro _ ⟨z, hz, rfl⟩
  have he := nestedEval_toNested P z (star z)
  rw [hC] at he
  simpa [nestedEval, Polynomial.IsRoot, r, realLocus] using he.trans hz
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P Q : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) (hsub : realLocus P ⊆ realLocus Q) : P ∣ Q := by
  by_contra hnot
  have hirr : Irreducible (toNested P) := hP.map toNested.toMulEquiv
  have hndvd : ¬ toNested P ∣ toNested Q := by
    intro h
    exact hnot ((map_dvd_iff toNested).mp h)
  obtain ⟨A, B, r, hr, hidentity⟩ := elimination_identity hirr
    (nested_degree_ne_zero hP.ne_zero hinf) hndvd
  apply infinite_conjugate_image hinf
  apply (Polynomial.finite_setOfPred_isRoot hr).subset
  rintro _ ⟨z, hz, rfl⟩
  have hp : nestedEval z (star z) (toNested P) = 0 :=
    (nestedEval_toNested P z (star z)).trans hz
  have hq : nestedEval z (star z) (toNested Q) = 0 :=
    (nestedEval_toNested Q z (star z)).trans (hsub hz)
  have he := congrArg (nestedEval z (star z)) hidentity
  simp only [map_add, map_mul, hp, hq, mul_zero, add_zero] at he
  simpa [nestedEval, Polynomial.IsRoot] using he.symm
end

#print axioms solution
