-- Prove2me | solution 1 for CurveSymmetry.direct_euclidean_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:40.062826+00:00
-- url     : https://prove2.me/submissions/744032a6-054e-4032-b344-8035432c6054

-- Solution generated from lean/DirectBound.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_anti_even_order
import Theorems.Thm_CurveSymmetry_anti_support
import Theorems.Thm_CurveSymmetry_centeredRotationGroup_finite
import Theorems.Thm_CurveSymmetry_direct_symmetries_common_center
import Theorems.Thm_CurveSymmetry_irreducible_radial_form
import Theorems.Thm_CurveSymmetry_not_irreducible_pure_powers
import Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
import Theorems.Thm_CurveSymmetry_rotation_sign_of_realLocus
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
/-- The homogeneous endpoint of the anti-invariant support calculation. -/
lemma anti_two_normal_form {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hdeg : P.totalDegree ≤ m + 1) (hanti : rotate ζ P = -P) :
    P = C (P.coeff (exponent m 0)) * (X 0 : BPoly) ^ m +
      C (P.coeff (exponent 0 m)) * X 1 ^ m := by
  classical
  have hsupp : ∀ s ∈ P.support, s = exponent m 0 ∨ s = exponent 0 m := by
    intro s hs
    have hd := support_degree hs
    have hw := anti_support (by omega) hζ (by omega) hanti hs
    simp only [exponent_eq_iff]
    omega
  have hne : exponent m 0 ≠ exponent 0 m := by simp [exponent_eq_iff]; omega
  have hform : P = monomial (exponent m 0) (P.coeff (exponent m 0)) +
      monomial (exponent 0 m) (P.coeff (exponent 0 m)) := by
    ext s
    by_cases hs : s ∈ P.support
    · rcases hsupp s hs with rfl | rfl <;> simp [coeff_monomial, hne, Ne.symm hne]
    · have hc : P.coeff s = 0 := notMem_support_iff.mp hs
      simp only [MvPolynomial.coeff_add, coeff_monomial]
      split_ifs <;> simp_all
  simpa [monomial_exponent] using hform
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Irreducibility now supplies the formerly explicit non-homogeneity exclusion. -/
theorem irreducible_anti_degree_gap {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly}
    (hirr : Irreducible P) (hanti : rotate ζ P = -P) : m + 2 ≤ P.totalDegree := by
  by_contra h
  have hform := anti_two_normal_form hm hζ (by omega) hanti
  rw [hform] at hirr
  exact not_irreducible_pure_powers m hm _ _ hirr
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A polynomial version of the bound with irreducibility, not non-homogeneity,
as a hypothesis. The only excluded polynomial shapes are the radial conics. -/
theorem irreducible_rotation_bound {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {P : BPoly} (hirr : Irreducible P)
    (hd : 2 ≤ P.totalDegree)
    (hnonradial : ¬ ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r))
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  by_cases hsmall : N ≤ P.totalDegree
  · exact le_trans hsmall (le_max_left _ _)
  have hlarge : P.totalDegree < N := by omega
  rcases hsign with hfixed | hanti
  · exact (hnonradial (irreducible_radial_form hirr
      (fun _ hs => fixed_support hζ hlarge hfixed hs))).elim
  · obtain ⟨m, hN⟩ := anti_even_order hζ hirr.ne_zero hanti
    have horder : N = 2 * m := by omega
    have hgap := irreducible_anti_degree_gap (by omega) (horder ▸ hζ) hirr hanti
    exact le_trans (by omega : N ≤ 2 * P.totalDegree - 4) (le_max_right _ _)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The centered rotation bound with actual irreducibility and a non-circle real locus.

The remaining polynomial-level input is the sign transformation identity.
-/
theorem realLocus_rotation_bound {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {P : BPoly} (hirr : Irreducible P) (hd : 2 ≤ P.totalDegree)
    (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    (hsign : rotate ζ P = P ∨ rotate ζ P = -P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  apply irreducible_rotation_bound hζ hirr hd _ hsign
  intro hradial
  exact hcircle (radial_realLocus_is_circle hinf hradial)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A genuine zero-set rotation bound: no polynomial sign or support hypotheses remain. -/
theorem geometric_rotation_order_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    {N : ℕ} (hN : N ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hsym : ∀ z ∈ realLocus P, ζ * z ∈ realLocus P) :
    N ≤ max P.totalDegree (2 * P.totalDegree - 4) :=
  realLocus_rotation_bound hζ hP hd hinf hcircle
    (rotation_sign_of_realLocus hP hinf (hζ.norm'_eq_one hN) hsym)
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
/-- The whole centered rotation group is finite cyclic and satisfies the sharp upper bound. -/
theorem centered_rotation_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R) :
    Finite (centeredRotationGroup P) ∧ IsCyclic (centeredRotationGroup P) ∧
      Nat.card (centeredRotationGroup P) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  refine ⟨inferInstance, inferInstance, ?_⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (Nat.card (centeredRotationGroup P)) := by
    rw [← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  exact geometric_rotation_order_bound hP hd hinf hcircle (Nat.card_pos.ne') hroot
    (fun z hz => (u.prop.2 z).mpr hz)
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

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (DirectSymmetries P) ∧
      Nat.card (DirectSymmetries P) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  obtain ⟨c, hc⟩ := direct_symmetries_common_center hP hd hinf.nonempty
  have hirr : Irreducible (shift c P) := hP.map (shiftEquiv c).toMulEquiv
  have hdegree : 2 ≤ (shift c P).totalDegree := by simpa [shift_degree] using hd
  obtain ⟨hf, _, hb⟩ := centered_rotation_group_bound hirr hdegree
    (realLocus_shift_infinite c hinf) (shifted_not_circle c hcircle)
  let := hf
  have hfinite : Finite (DirectSymmetries P) :=
    Finite.of_injective (directRotationEquiv P c hc) (directRotationEquiv P c hc).injective
  refine ⟨hfinite, ?_⟩
  rw [Nat.card_congr (directRotationEquiv P c hc)]
  simpa [shift_degree] using hb
end

#print axioms solution
