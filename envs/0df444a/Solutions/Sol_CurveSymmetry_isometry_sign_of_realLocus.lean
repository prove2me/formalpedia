-- Prove2me | solution 1 for CurveSymmetry.isometry_sign_of_realLocus
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:35.84058+00:00
-- url     : https://prove2.me/submissions/7d895471-915b-4a6d-8706-c258f845b041

-- Solution generated from lean/IsometrySign.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_isometry_affine_forms
import Theorems.Thm_CurveSymmetry_no_translation_symmetry
import Theorems.Thm_CurveSymmetry_opposite_symmetry_fixed_point
import Theorems.Thm_CurveSymmetry_reflection_fixes_equation
import Theorems.Thm_CurveSymmetry_rotation_sign_of_realLocus
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
lemma eval_rotate (ζ : ℂ) (hnorm : ‖ζ‖ = 1) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (rotate ζ P) =
      eval (fun i : Fin 2 => if i = 0 then ζ * z else star (ζ * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rotate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [rotate, Complex.inv_eq_conj hnorm, star_mul, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_zero (P : BPoly) : shift 0 P = P := by
  simp [shift]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_comp (c d : ℂ) (P : BPoly) : shift c (shift d P) = shift (c + d) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [shift]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [shift, star_add, map_add, add_assoc]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable def shiftEquiv (c : ℂ) : BPoly ≃+* BPoly :=
  { shift c with
    invFun := shift (-c)
    left_inv := fun P => by
      change shift (-c) (shift c P) = P
      rw [shift_comp, neg_add_cancel, shift_zero]
    right_inv := fun P => by
      change shift c (shift (-c) P) = P
      rw [shift_comp, add_neg_cancel, shift_zero] }
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma totalDegree_sum_le {ι : Type*} (s : Finset ι) (F : ι → BPoly) (d : ℕ)
    (h : ∀ i ∈ s, (F i).totalDegree ≤ d) : (∑ i ∈ s, F i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (totalDegree_add _ _).trans (max_le (h a (by simp))
        (ih (fun i hi => h i (by simp [hi]))))
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_monomial (c a : ℂ) (s : Exponent) :
    shift c (monomial s a) = C a * ((X 0 : BPoly) + C c) ^ s 0 *
      (X 1 + C (star c)) ^ s 1 := by
  simp only [shift, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp [mul_assoc]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_degree_le (c : ℂ) (P : BPoly) : (shift c P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_sum_le
  intro s hs
  rw [shift_monomial]
  have h0 := totalDegree_add (X 0 : BPoly) (C c)
  have h1 := totalDegree_add (X 1 : BPoly) (C (star c))
  simp only [totalDegree_X, totalDegree_C, max_eq_left (by omega : 0 ≤ 1)] at h0 h1
  have hp0 := (totalDegree_pow ((X 0 : BPoly) + C c) (s 0)).trans
    (Nat.mul_le_mul_left (s 0) h0)
  have hp1 := (totalDegree_pow ((X 1 : BPoly) + C (star c)) (s 1)).trans
    (Nat.mul_le_mul_left (s 1) h1)
  have hm0 := totalDegree_mul (C (P.coeff s) : BPoly) ((X 0 + C c) ^ s 0)
  have hm1 := totalDegree_mul (C (P.coeff s) * (X 0 + C c) ^ s 0 : BPoly)
    ((X 1 + C (star c)) ^ s 1)
  simp only [totalDegree_C, zero_add, Nat.mul_one] at hp0 hp1 hm0
  have hd := support_degree hs
  omega
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_degree (c : ℂ) (P : BPoly) : (shift c P).totalDegree = P.totalDegree := by
  apply le_antisymm (shift_degree_le c P)
  have h := shift_degree_le (-c) (shift c P)
  simpa [shift_comp, shift_zero] using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_shift (c : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (shift c P) =
      eval (fun i : Fin 2 => if i = 0 then z + c else star (z + c)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [shift]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [shift, star_add]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mem_realLocus_shift (c : ℂ) (P : BPoly) (z : ℂ) :
    z ∈ realLocus (shift c P) ↔ z + c ∈ realLocus P := by
  change eval _ (shift c P) = 0 ↔ _
  rw [eval_shift]
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma realLocus_shift_infinite (c : ℂ) {P : BPoly} (hinf : (realLocus P).Infinite) :
    (realLocus (shift c P)).Infinite := by
  have h := hinf.image (f := fun z : ℂ => z - c) (by
    intro x _ y _ h; exact sub_left_injective h)
  apply h.mono
  rintro _ ⟨z, hz, rfl⟩
  simpa [mem_realLocus_shift] using hz
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_reflect (a : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (reflect a P) =
      eval (fun i : Fin 2 => if i = 0 then a * star z else star (a * star z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [reflect, star_mul, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_ne_opposite {a b c d : ℂ} (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * z + b = c * star z + d) : False := by
  have h0 := h 0
  have h1 := h 1
  have hI := h Complex.I
  simp only [star_zero, mul_zero, zero_add] at h0
  simp only [star_one, mul_one] at h1
  have hac : a = c := by linear_combination h1 - h0
  have he : a * Complex.I = a * (-Complex.I) := by
    simpa [← hac, h0] using hI
  have hi := congrArg Complex.im (mul_left_cancel₀ ha he)
  norm_num at hi
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (T : isometrySymmetryGroup P) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then T.val z else star (T.val z)) P =
        ε * eval (fun i : Fin 2 => if i = 0 then z else star z) P) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by
  have hT : ∀ z, T.val z ∈ realLocus P ↔ z ∈ realLocus P := T.prop
  rcases isometry_affine_forms T.val with ⟨a, b, ha, he⟩ | ⟨a, b, ha, he⟩
  · have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    have hnotopp : ¬ ∃ c d : ℂ, ∀ z : ℂ, T.val z = c * star z + d := by
      rintro ⟨c, d, hcd⟩
      exact direct_ne_opposite ha0 (fun z => (he z).symm.trans (hcd z))
    by_cases ha1 : a = 1
    · have hb : b = 0 := by
        apply no_translation_symmetry hP hd hinf.nonempty
        intro z hz
        have h := (hT z).mpr hz
        rwa [he, ha1, one_mul] at h
      refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
      rw [he, ha1, hb, one_mul, add_zero, one_mul]
    · have h1a : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      set z0 := b / (1 - a) with hz0
      have hmap : ∀ z, T.val z = a * (z - z0) + z0 := by
        intro z
        rw [he, hz0]
        field_simp
        ring
      have hQ : Irreducible (shift z0 P) := hP.map (shiftEquiv z0).toMulEquiv
      have hQinf := realLocus_shift_infinite z0 hinf
      have hsym : ∀ z ∈ realLocus (shift z0 P), a * z ∈ realLocus (shift z0 P) := by
        intro z hz
        rw [mem_realLocus_shift] at hz ⊢
        have h := (hT (z + z0)).mpr hz
        rwa [hmap, add_sub_cancel_right] at h
      have hval : ∀ z, eval (fun i : Fin 2 => if i = 0 then T.val z else star (T.val z)) P =
          eval (fun i : Fin 2 => if i = 0 then z - z0 else star (z - z0))
            (rotate a (shift z0 P)) := by
        intro z
        rw [eval_rotate a ha, eval_shift, ← hmap]
      have hback : ∀ z, eval (fun i : Fin 2 => if i = 0 then z - z0 else star (z - z0))
          (shift z0 P) = eval (fun i : Fin 2 => if i = 0 then z else star z) P := by
        intro z
        rw [eval_shift, sub_add_cancel]
      rcases rotation_sign_of_realLocus hQ hQinf ha hsym with hr | hr
      · refine ⟨1, Or.inl rfl, fun z => ?_, fun h => (hnotopp h).elim⟩
        rw [hval, hr, hback, one_mul]
      · refine ⟨-1, Or.inr rfl, fun z => ?_, fun h => (hnotopp h).elim⟩
        rw [hval, hr, map_neg, hback, neg_one_mul]
  · have hS : OppositeSymmetry (realLocus P) a b := ⟨ha, fun z => by rw [← he]; exact hT z⟩
    have hfixed := opposite_symmetry_fixed_point hP hd hinf.nonempty hS
    set z0 := b / 2 with hz0
    have hmap : ∀ z, T.val z = a * star (z - z0) + z0 := by
      intro z
      rw [he, star_sub, mul_sub]
      linear_combination hfixed
    have hQ : Irreducible (shift z0 P) := hP.map (shiftEquiv z0).toMulEquiv
    have hQinf := realLocus_shift_infinite z0 hinf
    have hsym : ∀ z ∈ realLocus (shift z0 P), a * star z ∈ realLocus (shift z0 P) := by
      intro z hz
      rw [mem_realLocus_shift] at hz ⊢
      have h := (hT (z + z0)).mpr hz
      rwa [hmap, add_sub_cancel_right] at h
    have hfix := reflection_fixes_equation hQ (by rwa [shift_degree]) hQinf ha hsym
    refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
    have h := eval_reflect a (shift z0 P) (z - z0)
    rw [hfix, eval_shift, eval_shift, sub_add_cancel, ← hmap] at h
    rw [← h, one_mul]
end

#print axioms solution
