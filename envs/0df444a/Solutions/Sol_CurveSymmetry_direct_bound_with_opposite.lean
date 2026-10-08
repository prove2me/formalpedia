-- Prove2me | solution 1 for CurveSymmetry.direct_bound_with_opposite
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:39.186151+00:00
-- url     : https://prove2.me/submissions/4ad46b28-6a4d-4446-8b2d-6b53aadb786b

-- Solution generated from lean/ReflectionBound.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_centeredRotationGroup_finite
import Theorems.Thm_CurveSymmetry_direct_symmetries_common_center
import Theorems.Thm_CurveSymmetry_irreducible_radial_form
import Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
import Theorems.Thm_CurveSymmetry_reflection_fixes_equation
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
lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma opposite_comp_opposite {S : Set ℂ} {a b c d : ℂ}
    (h1 : OppositeSymmetry S a b) (h2 : OppositeSymmetry S c d) :
    DirectSymmetry S (a * star c) (a * star d + b) := by
  refine ⟨by simp [h1.1, h2.1], ?_⟩
  intro z
  have he : a * star c * z + (a * star d + b) = a * star (c * star z + d) + b := by
    simp only [star_add, star_mul, star_star]
    ring
  rw [he]
  exact (h1.2 (c * star z + d)).trans (h2.2 z)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma opposite_comp_direct {S : Set ℂ} {a b c d : ℂ}
    (h1 : OppositeSymmetry S a b) (h2 : DirectSymmetry S c d) :
    OppositeSymmetry S (a * star c) (a * star d + b) := by
  refine ⟨by simp [h1.1, h2.1], ?_⟩
  intro z
  have he : a * star c * star z + (a * star d + b) = a * star (c * z + d) + b := by
    simp only [star_add, star_mul]
    ring
  rw [he]
  exact (h1.2 (c * z + d)).trans (h2.2 z)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma opposite_inverse {S : Set ℂ} {a b : ℂ} (h : OppositeSymmetry S a b) :
    OppositeSymmetry S a (-a * star b) := by
  have hc := mul_star_eq_one_of_norm h.1
  refine ⟨h.1, ?_⟩
  intro z
  have he : a * star (a * star z + -a * star b) + b = z := by
    simp only [star_add, star_mul, star_star, star_neg]
    linear_combination (z - b) * hc
  exact (he ▸ h.2 (a * star z + -a * star b)).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma opposite_shift {P : BPoly} {a b c : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) :
    OppositeSymmetry (realLocus (shift c P)) a (a * star c + b - c) := by
  refine ⟨h.1, ?_⟩
  intro z
  rw [mem_realLocus_shift, mem_realLocus_shift]
  have he : a * star z + (a * star c + b - c) + c = a * star (z + c) + b := by
    simp only [star_add]
    ring
  rw [he]
  exact h.2 (z + c)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
/-- If a nonidentity direct rotation is centered at zero, every opposite symmetry
is centered there too. -/
lemma opposite_centered {P : BPoly}
    (hcenter : ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = 0)
    {r : ℂ} (hr : r ≠ 1) (hrot : DirectSymmetry (realLocus P) r 0)
    {a b : ℂ} (hg : OppositeSymmetry (realLocus P) a b) : b = 0 := by
  have ha := mul_star_eq_one_of_norm hg.1
  have hconj := opposite_comp_opposite
    (opposite_comp_direct hg hrot) (opposite_inverse hg)
  have he := hcenter _ _ hconj
  simp only [star_neg, star_mul, star_star, star_zero, mul_zero, zero_add] at he
  have he' : (1 - star r) * b = 0 := by
    linear_combination he + star r * b * ha
  have hn : 1 - star r ≠ 0 := by
    intro h
    apply hr
    have hs : star r = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg star hs
  exact (mul_eq_zero.mp he').resolve_left hn
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma reflect_pair {a r : ℂ} (ha : ‖a‖ = 1) (hr : ‖r‖ = 1) (P : BPoly) :
    reflect a (reflect (r * a) P) = rotate r P := by
  have hc := mul_star_eq_one_of_norm ha
  have h0 : ∀ b : ℂ, reflect b (X 0) = C b * X 1 := by intro b; simp [reflect]
  have h1 : ∀ b : ℂ, reflect b (X 1) = C (star b) * X 0 := by intro b; simp [reflect]
  have hC : ∀ b c : ℂ, reflect b (C c) = C c := by intro b c; simp [reflect]
  have he0 : r * a * star a = r := by linear_combination r * hc
  have he1 : star (r * a) * a = r⁻¹ := by
    change (starRingEnd ℂ) (r * a) * a = r⁻¹
    rw [Complex.inv_eq_conj hr]
    change star (r * a) * a = star r
    simp only [star_mul]
    linear_combination star r * hc
  induction P using MvPolynomial.induction_on with
  | C c => simp [reflect, rotate]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change rotate r P * reflect a (reflect (r * a) (X 0)) = rotate r P * rotate r (X 0)
        rw [h0, map_mul, hC, h1, ← mul_assoc (C (r * a)), ← C_mul, he0]
        simp [rotate]
      · change rotate r P * reflect a (reflect (r * a) (X 1)) = rotate r P * rotate r (X 1)
        rw [h1, map_mul, hC, h0, ← mul_assoc (C (star (r * a))), ← C_mul, he1]
        simp [rotate]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma rotation_fixes_equation_with_reflection {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    {a : ℂ} (ha : OppositeSymmetry (realLocus P) a 0)
    (u : centeredRotationGroup P) : rotate (u.val : ℂ) P = P := by
  have hfirst := reflection_fixes_equation hP hd hinf ha.1 (by
    intro z hz
    simpa using (ha.2 z).mpr hz)
  have hnorm : ‖(u.val : ℂ) * a‖ = 1 := by simp [u.prop.1, ha.1]
  have hsecond := reflection_fixes_equation hP hd hinf hnorm (by
    intro z hz
    have h := (u.prop.2 (a * star z)).mpr (by simpa using (ha.2 z).mpr hz)
    simpa [mul_assoc] using h)
  rw [← reflect_pair ha.1 u.prop.1, hsecond, hfirst]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A centered reflection improves the rotation bound from `max(d,2d-4)` to `d`. -/
theorem centered_rotation_bound_with_reflection {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (hcircle : ¬ ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R)
    {a : ℂ} (ha : OppositeSymmetry (realLocus P) a 0) :
    Nat.card (centeredRotationGroup P) ≤ P.totalDegree := by
  let := centeredRotationGroup_finite hP hinf hcircle
  let := isCyclic_of_injective_ringHom (rotationValue P) (rotationValue_injective P)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := centeredRotationGroup P)
  have hroot : IsPrimitiveRoot (rotationValue P u) (Nat.card (centeredRotationGroup P)) := by
    rw [← hu]
    exact (IsPrimitiveRoot.orderOf u).map_of_injective (rotationValue_injective P)
  by_contra h
  obtain ⟨a, b, hab, hc⟩ := exists_off_diagonal_coeff hP hinf hcircle
  have hs := fixed_support hroot (by omega)
    (rotation_fixes_equation_with_reflection hP hd hinf ha u) (mem_support_iff.mpr hc)
  exact hab (by simpa using hs)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma shift_centered {P : BPoly} {c : ℂ}
    (hc : ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * c) :
    ∀ a b : ℂ, DirectSymmetry (realLocus (shift c P)) a b → b = 0 := by
  intro a b h
  have hback : DirectSymmetry (realLocus P) a (b + c - a * c) := by
    refine ⟨h.1, ?_⟩
    intro z
    have he := h.2 (z - c)
    rw [mem_realLocus_shift, mem_realLocus_shift] at he
    have he' : a * (z - c) + b + c = a * z + (b + c - a * c) := by ring
    simpa only [he', sub_add_cancel] using he
  have he := hc _ _ hback
  linear_combination he
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P)
    (g : OppositeSymmetries P) : Nat.card (DirectSymmetries P) ≤ P.totalDegree := by
  classical
  obtain ⟨c, hc⟩ := direct_symmetries_common_center hP hd hinf.nonempty
  have hirr : Irreducible (shift c P) := hP.map (shiftEquiv c).toMulEquiv
  have hdegree : 2 ≤ (shift c P).totalDegree := by simpa [shift_degree] using hd
  have hi := realLocus_shift_infinite c hinf
  have hn := shifted_not_circle c hcircle
  rw [Nat.card_congr (directRotationEquiv P c hc)]
  let := centeredRotationGroup_finite hirr hi hn
  by_cases hex : ∃ u : centeredRotationGroup (shift c P), (u.val : ℂ) ≠ 1
  · obtain ⟨u, hu⟩ := hex
    have hrot : DirectSymmetry (realLocus (shift c P)) (u.val : ℂ) 0 :=
      ⟨u.prop.1, by simpa using u.prop.2⟩
    have hg := opposite_shift (c := c) g.prop
    have hb := opposite_centered (shift_centered hc) hu hrot hg
    rw [hb] at hg
    simpa [shift_degree] using centered_rotation_bound_with_reflection hirr hdegree hi hn hg
  · have hsub : Subsingleton (centeredRotationGroup (shift c P)) := by
      refine ⟨fun u v => rotationValue_injective _ ?_⟩
      have hu : (u.val : ℂ) = 1 := by by_contra h; exact hex ⟨u, h⟩
      have hv : (v.val : ℂ) = 1 := by by_contra h; exact hex ⟨v, h⟩
      exact hu.trans hv.symm
    let := hsub
    have he : Nat.card (centeredRotationGroup (shift c P)) = 1 := Nat.card_unique
    omega
end

#print axioms solution
