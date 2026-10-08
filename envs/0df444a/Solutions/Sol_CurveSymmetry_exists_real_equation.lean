-- Prove2me | solution 1 for CurveSymmetry.exists_real_equation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:14.255774+00:00
-- url     : https://prove2.me/submissions/5c6b26b2-316e-45df-9b59-8f66e2d290e9

-- Solution generated from lean/RealEquation.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Theorems.Thm_CurveSymmetry_no_translation_symmetry
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
/-- A same-degree equation vanishing on the real curve differs by a nonzero scalar. -/
theorem proportional_of_realLocus_subset {P Q : BPoly} (hP : Irreducible P)
    (hQ : Q ≠ 0) (hinf : (realLocus P).Infinite)
    (hsub : realLocus P ⊆ realLocus Q) (hdeg : Q.totalDegree ≤ P.totalDegree) :
    ∃ c : ℂ, c ≠ 0 ∧ Q = C c * P := by
  obtain ⟨S, hS⟩ := dvd_of_realLocus_subset hP hinf hsub
  have hs0 : S ≠ 0 := by intro hs; apply hQ; simp [hS, hs]
  have hdegree := totalDegree_mul_of_isDomain hP.ne_zero hs0
  have hdS : S.totalDegree = 0 := by rw [← hS] at hdegree; omega
  have hcS : S = C (S.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdS
  refine ⟨S.coeff 0, ?_, ?_⟩
  · intro hc
    exact hs0 (by simpa [hc] using hcS)
  · rw [hS, hcS, mul_comm]
    simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coeff_conjugateSwap (P : BPoly) (a b : ℕ) :
    (conjugateSwap P).coeff (exponent b a) = star (P.coeff (exponent a b)) := by
  have he : (exponent a b).mapDomain (Equiv.swap (0 : Fin 2) 1) = exponent b a := by
    simp [exponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, add_comm]
  simp only [conjugateSwap, RingHom.comp_apply, coeff_map]
  change star ((rename (Equiv.swap (0 : Fin 2) 1) P).coeff (exponent b a)) = _
  rw [← he, coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 2) 1).injective]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugateSwap_ne_zero {P : BPoly} (hP : P ≠ 0) : conjugateSwap P ≠ 0 := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  intro hzero
  have h := coeff_conjugateSwap P (s 0) (s 1)
  rw [hzero, MvPolynomial.coeff_zero] at h
  apply hs
  rw [he]
  exact star_eq_zero.mp h.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugateSwap_degree_le (P : BPoly) : (conjugateSwap P).totalDegree ≤ P.totalDegree := by
  exact (totalDegree_le_of_support_subset (support_map_subset _ _)).trans
    (totalDegree_rename_le _ _)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_conjugateSwap (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (conjugateSwap P) =
      star (eval (fun i : Fin 2 => if i = 0 then z else star z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [conjugateSwap]
  | add P Q hP hQ => simp only [map_add, hP, hQ, star_add]
  | mul_X P i hP =>
      simp only [map_mul, hP, star_mul]
      fin_cases i <;> simp [conjugateSwap, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma exists_nonzero_real_evaluation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ z : ℂ, eval (fun i : Fin 2 => if i = 0 then z else star z) P ≠ 0 := by
  by_contra h
  push Not at h
  have ht := no_translation_symmetry hP hd hinf.nonempty (v := 1) (by
    intro z _
    exact h (z + 1))
  norm_num at ht
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a b : ℕ,
      (C c * P).coeff (exponent b a) = star ((C c * P).coeff (exponent a b)) := by
  obtain ⟨z, hz⟩ := exists_nonzero_real_evaluation hP hd hinf
  let v := eval (fun i : Fin 2 => if i = 0 then z else star z) P
  have hv : v ≠ 0 := hz
  have hsub : realLocus P ⊆ realLocus (conjugateSwap P) := by
    intro w hw
    change eval _ (conjugateSwap P) = 0
    rw [eval_conjugateSwap, hw, star_zero]
  obtain ⟨k, _, hk⟩ := proportional_of_realLocus_subset hP
    (conjugateSwap_ne_zero hP.ne_zero) hinf hsub (conjugateSwap_degree_le P)
  have he := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) hk
  rw [eval_conjugateSwap, map_mul, eval_C] at he
  change star v = k * v at he
  have hscaled : conjugateSwap (C v⁻¹ * P) = C v⁻¹ * P := by
    have hC : conjugateSwap (C v⁻¹) = C (star (v⁻¹)) := by simp [conjugateSwap]
    rw [map_mul, hC, hk, ← mul_assoc, ← C_mul]
    congr 2
    change (starRingEnd ℂ) (v⁻¹) * k = v⁻¹
    rw [map_inv₀]
    change (star v)⁻¹ * k = v⁻¹
    apply (mul_right_cancel₀ hv)
    rw [mul_assoc, ← he, inv_mul_cancel₀ (star_ne_zero.mpr hv), inv_mul_cancel₀ hv]
  refine ⟨v⁻¹, inv_ne_zero hv, ?_⟩
  intro a b
  have h := coeff_conjugateSwap (C v⁻¹ * P) a b
  rwa [hscaled] at h
end

#print axioms solution
