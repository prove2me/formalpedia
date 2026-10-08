-- Prove2me | solution 1 for CurveSymmetry.paper_equality_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:52.597986+00:00
-- url     : https://prove2.me/submissions/6fb1d662-0cdd-4dc4-ad5f-ab6aae0d3175

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_anti_support
import Theorems.Thm_CurveSymmetry_cartesianize_complexify
import Theorems.Thm_CurveSymmetry_centeredRotationGroup_finite
import Theorems.Thm_CurveSymmetry_complexify_cartesianize
import Theorems.Thm_CurveSymmetry_direct_symmetries_common_center
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_exists_real_equation
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_irreducible_radial_form
import Theorems.Thm_CurveSymmetry_linear_substitution_degree_le
import Theorems.Thm_CurveSymmetry_normalize_twoParameter
import Theorems.Thm_CurveSymmetry_not_irreducible_pure_powers
import Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
import Theorems.Thm_CurveSymmetry_rotation_sign_of_realLocus
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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotate_monomial (ζ : ℂ) (s : Exponent) (c : ℂ) :
    rotate ζ (monomial s c) = monomial s (c * (ζ ^ s 0 * (ζ⁻¹) ^ s 1)) := by
  simp only [rotate, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, mul_pow,
    ← map_pow C, X_pow_eq_monomial]
  rw [show s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) from exponent_decompose s]
  simp only [C_mul_monomial, monomial_mul, mul_one]
  simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coeff_rotate (ζ : ℂ) (P : BPoly) (s : Exponent) :
    (rotate ζ P).coeff s = P.coeff s * (ζ ^ s 0 * (ζ⁻¹) ^ s 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial t c =>
      rw [rotate_monomial]
      by_cases h : t = s
      · subst t; simp
      · simp [coeff_monomial, h]
  | add P Q hP hQ => simp [map_add, hP, hQ, add_mul]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- At degree at most `m+2`, there are only four possible monomials. -/
theorem anti_four_support {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    {s : Exponent} (hs : s ∈ P.support) :
    s = exponent m 0 ∨ s = exponent (m + 1) 1 ∨
      s = exponent 0 m ∨ s = exponent 1 (m + 1) := by
  have hd := support_degree hs
  have hw := anti_support (by omega) hζ (by omega) hanti hs
  simp only [exponent_eq_iff]
  omega
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The four-term normal form, with its coefficients extracted from `P`. -/
theorem anti_four_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P) :
    P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
      monomial (exponent (m + 1) 1) (P.coeff (exponent (m + 1) 1)) +
      monomial (exponent 0 m) (P.coeff (exponent 0 m)) +
      monomial (exponent 1 (m + 1)) (P.coeff (exponent 1 (m + 1))) := by
  classical
  have h01 : exponent m 0 ≠ exponent (m + 1) 1 := by
    simp [exponent_eq_iff]
  have h02 : exponent m 0 ≠ exponent 0 m := by
    simp [exponent_eq_iff]; omega
  have h03 : exponent m 0 ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]
  have h12 : exponent (m + 1) 1 ≠ exponent 0 m := by
    simp [exponent_eq_iff]
  have h13 : exponent (m + 1) 1 ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]; omega
  have h23 : exponent 0 m ≠ exponent 1 (m + 1) := by
    simp [exponent_eq_iff]
  ext s
  by_cases hs : s ∈ P.support
  · rcases anti_four_support hm hζ hdeg hanti hs with rfl | rfl | rfl | rfl <;>
      simp [coeff_monomial, h01, h02, h03, h12, h13, h23,
        Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  · have hc : P.coeff s = 0 := notMem_support_iff.mp hs
    simp only [MvPolynomial.coeff_add, coeff_monomial]
    split_ifs <;> simp_all
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Conjugate-symmetric coefficients give the two-parameter form used in the paper. -/
theorem anti_real_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ a b : ℂ, P = (X 0 : BPoly) ^ m * (C a + C b * X 0 * X 1) +
      X 1 ^ m * (C (star a) + C (star b) * X 0 * X 1) := by
  refine ⟨P.coeff (exponent m 0), P.coeff (exponent (m + 1) 1), ?_⟩
  calc
    P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
        monomial (exponent (m + 1) 1) (P.coeff (exponent (m + 1) 1)) +
        monomial (exponent 0 m) (star (P.coeff (exponent m 0))) +
        monomial (exponent 1 (m + 1)) (star (P.coeff (exponent (m + 1) 1))) := by
          conv_lhs => rw [anti_four_normal_form hm hζ hdeg hanti]
          rw [hreal m 0, hreal (m + 1) 1]
    _ = _ := by simp only [monomial_exponent, pow_zero, pow_succ]; ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A polynomial fixed by a rotation of order greater than its degree is radial. -/
theorem fixed_support {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {P : BPoly}
    (hdeg : P.totalDegree < N) (hfixed : rotate ζ P = P)
    {s : Exponent} (hs : s ∈ P.support) : s 0 = s 1 := by
  have hc : P.coeff s ≠ 0 := mem_support_iff.mp hs
  have hd := support_degree hs
  have hz : ζ ≠ 0 := hζ.ne_zero (by omega)
  have heq := congrArg (fun Q : BPoly => Q.coeff s) hfixed
  rw [coeff_rotate] at heq
  have hchar : ζ ^ s 0 * (ζ⁻¹) ^ s 1 = 1 := by
    apply mul_left_cancel₀ hc
    simpa using heq
  rw [inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hz)] at hchar
  exact hζ.pow_inj (by omega) (by omega) hchar
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma radial_factor_not_isUnit (r : ℂ) : ¬ IsUnit ((X 0 : BPoly) * X 1 - C r) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then r else 1))
  simp at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotationValue_injective (P : BPoly) : Function.Injective (rotationValue P) := by
  intro u v h
  apply Subtype.ext
  exact Units.ext h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma exists_off_diagonal_coeff {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    ∃ a b : ℕ, a ≠ b ∧ P.coeff (exponent a b) ≠ 0 := by
  by_contra h
  push Not at h
  apply hcircle
  apply radial_realLocus_is_circle hinf
  apply irreducible_radial_form hP
  intro s hs
  by_contra hne
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  exact (mem_support_iff.mp hs) (by rw [he]; exact h (s 0) (s 1) hne)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_coeff_ne_zero {S : Set ℂ} {a b : ℂ} (h : DirectSymmetry S a b) : a ≠ 0 := by
  intro hz
  have hnorm := h.1
  simp [hz] at hnorm
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
lemma shifted_not_circle (c : ℂ) {P : BPoly} (hcircle : NotCircle P) :
    ¬ ∃ R : ℝ, 0 < R ∧ realLocus (shift c P) = Metric.sphere (0 : ℂ) R := by
  rintro ⟨R, hR, he⟩
  apply hcircle
  refine ⟨c, R, hR, ?_⟩
  ext z
  have h := congrArg (fun S : Set ℂ => z - c ∈ S) he
  simpa [mem_realLocus_shift, Metric.mem_sphere, dist_eq_norm] using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable def directRotationEquiv (P : BPoly) (c : ℂ)
    (hcenter : ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * c) :
    DirectSymmetries P ≃ centeredRotationGroup (shift c P) where
  toFun u := ⟨Units.mk0 u.val.1 (direct_coeff_ne_zero u.prop), ⟨u.prop.1, by
    intro z
    change u.val.1 * z ∈ realLocus (shift c P) ↔ z ∈ realLocus (shift c P)
    rw [mem_realLocus_shift, mem_realLocus_shift]
    have he : u.val.1 * z + c = u.val.1 * (z + c) + u.val.2 := by
      rw [hcenter _ _ u.prop]
      ring
    rw [he]
    exact u.prop.2 (z + c)⟩⟩
  invFun u := ⟨((u.val : ℂ), (1 - (u.val : ℂ)) * c), ⟨u.prop.1, by
    intro z
    have h := u.prop.2 (z - c)
    rw [mem_realLocus_shift, mem_realLocus_shift] at h
    have he : (u.val : ℂ) * (z - c) + c = (u.val : ℂ) * z + (1 - (u.val : ℂ)) * c := by ring
    simpa only [he, sub_add_cancel] using h⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (hcenter _ _ u.prop).symm
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma C_mul_irreducible {c : ℂ} (hc : c ≠ 0) {P : BPoly} (hP : Irreducible P) :
    Irreducible (C c * P) :=
  (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hc).map C)).mpr hP
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma twoParameter_top_ne_zero {m : ℕ} (hm : 2 ≤ m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : b ≠ 0 := by
  intro hb
  apply not_irreducible_pure_powers m hm a (star a)
  simpa [twoParameter, hb, mul_comm] using hP
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma binary_sum_not_isUnit {m : ℕ} (hm : 0 < m) (b : ℂ) :
    ¬ IsUnit (C b * (X 0 : BPoly) ^ m + C (star b) * X 1 ^ m) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => (0 : ℂ)))
  simp [hm.ne'] at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma twoParameter_low_ne_zero {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : a ≠ 0 := by
  intro ha
  have he : twoParameter m a b = ((X 0 : BPoly) * X 1) *
      (C b * X 0 ^ m + C (star b) * X 1 ^ m) := by
    simp only [twoParameter, ha, star_zero, C_0, zero_add]
    ring
  have hfirst : ¬ IsUnit ((X 0 : BPoly) * X 1) := by
    simpa using radial_factor_not_isUnit 0
  exact (hP.isUnit_or_isUnit he).elim hfirst (binary_sum_not_isUnit hm b)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A real coefficient ratio would give a radial factor. -/
lemma twoParameter_ratio_nonreal {m : ℕ} (hm : 2 ≤ m) {a b : ℂ}
    (hP : Irreducible (twoParameter m a b)) : a / b ≠ star (a / b) := by
  have hb := twoParameter_top_ne_zero hm hP
  intro hreal
  have hba : b * (a / b) = a := mul_div_cancel₀ _ hb
  have hbar : star b * (a / b) = star a := by
    have h := congrArg star hba
    simp only [star_mul, ← hreal] at h
    simpa [mul_comm] using h
  have he : twoParameter m a b = ((X 0 : BPoly) * X 1 + C (a / b)) *
      (C b * X 0 ^ m + C (star b) * X 1 ^ m) := by
    have he0 := congrArg (C : ℂ →+* BPoly) hba
    have he1 := congrArg (C : ℂ →+* BPoly) hbar
    rw [map_mul] at he0 he1
    dsimp [twoParameter]
    simp only [Complex.star_def] at he1 ⊢
    linear_combination -(X 0 : BPoly) ^ m * he0 - (X 1 : BPoly) ^ m * he1
  have hfirst : ¬ IsUnit ((X 0 : BPoly) * X 1 + C (a / b)) := by
    simpa using radial_factor_not_isUnit (-(a / b))
  exact (hP.isUnit_or_isUnit he).elim hfirst (binary_sum_not_isUnit (by omega) b)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The four-term support theorem plus irreducibility excludes every degenerate parameter. -/
theorem irreducible_anti_normal_form {m : ℕ} (hm : 3 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly} (hP : Irreducible P)
    (hdeg : P.totalDegree ≤ m + 2) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ a / b ≠ star (a / b) ∧ P = twoParameter m a b := by
  obtain ⟨a, b, he⟩ := anti_real_normal_form hm hζ hdeg hanti hreal
  change P = twoParameter m a b at he
  have hi : Irreducible (twoParameter m a b) := he ▸ hP
  exact ⟨a, b, twoParameter_low_ne_zero (by omega) hi, twoParameter_top_ne_zero (by omega) hi,
    twoParameter_ratio_nonreal (by omega) hi, he⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_dilate (c : ℂ) (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (dilate c P) =
      eval (fun i : Fin 2 => if i = 0 then c * z else star (c * z)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dilate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [dilate, star_mul, mul_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma centered_extremal_generator {m : ℕ} (hm : 3 ≤ m) {P : BPoly}
    (hP : Irreducible P) (hdeg : P.totalDegree = m + 2) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hcard : Nat.card (centeredRotationGroup P) = 2 * m) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 * m) ∧ rotate ζ P = -P := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (2 * m) := by
    rw [← hcard, ← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  refine ⟨rotationValue P u, hroot, ?_⟩
  rcases rotation_sign_of_realLocus hP hinf u.prop.1 (fun z hz => (u.prop.2 z).mpr hz) with h | h
  · obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
    have he := fixed_support hroot (by omega) h (mem_support_iff.mpr hc)
    exact (hab (by simpa using he)).elim
  · exact h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- An extremal centered curve is the normalized family after a nonzero complex dilation. -/
theorem centered_extremal_classification {m : ℕ} (hm : 3 ≤ m) {P : BPoly}
    (hP : Irreducible P) (hdeg : P.totalDegree = m + 2) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hcard : Nat.card (centeredRotationGroup P) = 2 * m) :
    ∃ c α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      ∀ z : ℂ, z ∈ realLocus (familyPolynomial m α) ↔ c * z ∈ realLocus P := by
  obtain ⟨ζ, hζ, hanti⟩ := centered_extremal_generator hm hP hdeg hinf hcircle hcard
  obtain ⟨s, hs, hreal⟩ := exists_real_equation hP (by omega) hinf
  have hirr := C_mul_irreducible hs hP
  have hdegree : (C s * P).totalDegree ≤ m + 2 := by
    have he := totalDegree_mul (C s : BPoly) P
    simpa [hdeg] using he
  have hanti' : rotate ζ (C s * P) = -(C s * P) := by
    rw [map_mul, hanti]
    simp [rotate]
  obtain ⟨a, b, _, hb, hab, hform⟩ := irreducible_anti_normal_form hm hζ hirr hdegree hanti' hreal
  obtain ⟨c, α, k, hc, hα, hαr, hk, hn⟩ := normalize_twoParameter (m := m) (by omega) hb hab
  have he : dilate c (C s * P) = C (k : ℂ) * familyPolynomial m α := by
    rw [hform]
    exact hn
  refine ⟨c, α, hc, hα, hαr, ?_⟩
  intro z
  have hv := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) he
  rw [eval_dilate, map_mul, eval_C, map_mul, eval_C] at hv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hz := congrArg (fun w : ℂ => w = 0) hv
  change eval _ (familyPolynomial m α) = 0 ↔ eval _ P = 0
  simpa only [mul_eq_zero, hs, hk0, false_or] using Iff.of_eq hz.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Equality classification for arbitrary centers, with an explicit direct similarity.
The map `z ↦ cz+t` sends the normalized family onto the original real locus. -/
theorem extremal_classification {P : BPoly} (hP : Irreducible P)
    (hd : 5 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P)
    (hcard : Nat.card (DirectSymmetries P) = 2 * P.totalDegree - 4) :
    ∃ c t α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      realLocus P = (fun z : ℂ => c * z + t) '' realLocus (familyPolynomial (P.totalDegree - 2) α) := by
  obtain ⟨t, ht⟩ := direct_symmetries_common_center hP (by omega) hinf.nonempty
  have hirr : Irreducible (shift t P) := hP.map (shiftEquiv t).toMulEquiv
  have hdegree : (shift t P).totalDegree = (P.totalDegree - 2) + 2 := by rw [shift_degree]; omega
  have hc : Nat.card (centeredRotationGroup (shift t P)) = 2 * (P.totalDegree - 2) := by
    rw [← Nat.card_congr (directRotationEquiv P t ht), hcard]
    omega
  obtain ⟨c, α, hc0, hα, hαr, he⟩ := centered_extremal_classification (by omega) hirr hdegree
    (realLocus_shift_infinite t hinf) (shifted_not_circle t hcircle) hc
  refine ⟨c, t, α, hc0, hα, hαr, ?_⟩
  ext z
  constructor
  · intro hz
    have hback : c * ((z - t) / c) + t = z := by rw [mul_div_cancel₀ _ hc0]; ring
    refine ⟨(z - t) / c, ?_, hback⟩
    rw [he, mem_realLocus_shift, hback]
    exact hz
  · rintro ⟨w, hw, rfl⟩
    exact (mem_realLocus_shift t P (c * w)).mp ((he w).mp hw)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * z + b = c * z + d) : (a, b) = (c, d) := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add] at h0
  simp only [mul_one] at h1
  apply Prod.ext
  · linear_combination h1 - h0
  · exact h0
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable def complexifyEquiv : BPoly ≃+* BPoly :=
  { complexify with
    invFun := cartesianize
    left_inv := cartesianize_complexify
    right_inv := complexify_cartesianize }
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma complexify_degree_le (P : BPoly) : (complexify P).totalDegree ≤ P.totalDegree := by
  apply linear_substitution_degree_le
  intro i
  have hsum := totalDegree_add (X 0 : BPoly) (X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (X 1)
  have hc0 := totalDegree_mul (C (1 / 2 : ℂ) : BPoly) (X 0 + X 1)
  have hc1 := totalDegree_mul (-C Complex.I * C (1 / 2 : ℂ) : BPoly) (X 0 - X 1)
  have hc2 := totalDegree_mul (-C Complex.I : BPoly) (C (1 / 2 : ℂ))
  simp only [totalDegree_C, totalDegree_neg, totalDegree_X, zero_add, max_self] at hsum hsub hc0 hc1 hc2
  split_ifs <;> omega
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma cartesianize_degree_le (P : BPoly) : (cartesianize P).totalDegree ≤ P.totalDegree := by
  apply linear_substitution_degree_le
  intro i
  have hc := totalDegree_mul (C Complex.I : BPoly) (X 1)
  have hsum := totalDegree_add (X 0 : BPoly) (C Complex.I * X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (C Complex.I * X 1)
  simp only [totalDegree_C, totalDegree_X, zero_add] at hc hsum hsub
  split_ifs <;> omega
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma complexify_degree (P : BPoly) : (complexify P).totalDegree = P.totalDegree := by
  apply le_antisymm (complexify_degree_le P)
  have h := cartesianize_degree_le (complexify P)
  rwa [cartesianize_complexify] at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma real_map_degree (f : RPoly) : (map Complex.ofRealHom f).totalDegree = f.totalDegree := by
  simp only [totalDegree, support_map_of_injective f (f := Complex.ofRealHom) Complex.ofReal_injective]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma complexifyReal_degree (f : RPoly) : (complexifyReal f).totalDegree = f.totalDegree := by
  rw [complexifyReal, complexify_degree, real_map_degree]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma complexifyReal_irreducible {f : RPoly} (hf : GeometricallyIrreducible f) :
    Irreducible (complexifyReal f) :=
  hf.map complexifyEquiv.toMulEquiv
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_real_map (f : RPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then (z.re : ℂ) else (z.im : ℂ))
      (map Complex.ofRealHom f) =
      (eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f : ℂ) := by
  rw [eval_map]
  have h := eval₂_comp Complex.ofRealHom (fun i : Fin 2 => if i = 0 then z.re else z.im) f
  simpa only [Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite] using h.symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma complexifyReal_locus (f : RPoly) : realLocus (complexifyReal f) = cartesianLocus f := by
  ext z
  change eval _ (complexify (map Complex.ofRealHom f)) = 0 ↔ eval _ f = 0
  rw [eval_complexify, eval_real_map, Complex.ofReal_eq_zero]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem cartesian_extremal_classification {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 5 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    (hcard : Nat.card (CartesianDirectSymmetries f) = 2 * f.totalDegree - 4) :
    ∃ c t α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      cartesianLocus f = (fun z : ℂ => c * z + t) ''
        realLocus (familyPolynomial (f.totalDegree - 2) α) := by
  have h := extremal_classification (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
    (by simpa only [DirectSymmetries, complexifyReal_locus, complexifyReal_degree] using hcard)
  simpa only [complexifyReal_locus, complexifyReal_degree] using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma directParametersToIsometry_bijective (P : BPoly) :
    Function.Bijective (directParametersToIsometry P) := by
  constructor
  · intro u v he
    apply Subtype.ext
    apply direct_parameters_unique
    intro z
    exact congrArg (fun f : directIsometryGroup (realLocus P) => f.val z) he
  · rintro ⟨f, hf, a, b, ha, he⟩
    have hab : DirectSymmetry (realLocus P) a b :=
      ⟨ha, fun z => by rw [← he]; exact hf z⟩
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    exact fun z => (he z).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable def directIsometryEquiv (P : BPoly) :
    DirectSymmetries P ≃ directIsometryGroup (realLocus P) :=
  Equiv.ofBijective (directParametersToIsometry P) (directParametersToIsometry_bijective P)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma cartesian_direct_card (f : RPoly) :
    Nat.card (CartesianDirectSymmetries f) = Nat.card (directIsometryGroup (cartesianLocus f)) := by
  have he := Nat.card_congr (directIsometryEquiv (complexifyReal f))
  simpa only [DirectSymmetries, complexifyReal_locus] using he
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 5 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    (hcard : Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * f.totalDegree - 4) :
    ∃ a b α : ℂ, a ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      (fun z : ℂ => a * z + b) '' cartesianLocus f = extremalCurve (f.totalDegree - 2) α := by
  obtain ⟨c, t, α, hc, hα, hαr, he⟩ := cartesian_extremal_classification hf hd hinf hnc
    ((cartesian_direct_card f).trans hcard)
  refine ⟨c⁻¹, -c⁻¹ * t, α, inv_ne_zero hc, hα, hαr, ?_⟩
  rw [he, ← family_locus_eq, Set.image_image]
  have hm : (fun z : ℂ => c⁻¹ * (c * z + t) + -c⁻¹ * t) = id := by
    funext z
    change _ = z
    calc
      c⁻¹ * (c * z + t) + -c⁻¹ * t = (c⁻¹ * c) * z := by ring
      _ = z := by rw [inv_mul_cancel₀ hc, one_mul]
  change (fun z : ℂ => c⁻¹ * (c * z + t) + -c⁻¹ * t) '' _ = _
  rw [hm, Set.image_id]
end

#print axioms solution
