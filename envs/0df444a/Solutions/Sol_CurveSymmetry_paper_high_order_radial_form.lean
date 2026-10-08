-- Prove2me | solution 1 for CurveSymmetry.paper_high_order_radial_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:54.017979+00:00
-- url     : https://prove2.me/submissions/3a92dc57-4a3a-41c0-b30b-e279134a172f

-- Solution generated from lean/RadialAntiForm.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Theorems.Thm_CurveSymmetry_anti_even_order
import Theorems.Thm_CurveSymmetry_cartesianize_complexify
import Theorems.Thm_CurveSymmetry_complexify_cartesianize
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_irreducible_anti_radial_form
import Theorems.Thm_CurveSymmetry_irreducible_radial_form
import Theorems.Thm_CurveSymmetry_linear_substitution_degree_le
import Theorems.Thm_CurveSymmetry_radial_realLocus_is_circle
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
@[simp] lemma cartesianize_C (c : ℂ) : cartesianize (C c) = C c := by simp [cartesianize]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma cartesianize_X_zero : cartesianize (X 0) = X 0 + C Complex.I * X 1 := by simp [cartesianize]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma cartesianize_X_one : cartesianize (X 1) = X 0 - C Complex.I * X 1 := by simp [cartesianize]
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
lemma cartesianize_conjugateSwap (P : BPoly) :
    map (starRingEnd ℂ) (cartesianize P) = cartesianize (conjugateSwap P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [conjugateSwap]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      congr 1
      fin_cases i <;> simp [conjugateSwap, sub_eq_add_neg]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A complexified real Cartesian equation has conjugate-symmetric coefficients. -/
lemma complexifyReal_conjugate_coeff (f : RPoly) (a b : ℕ) :
    (complexifyReal f).coeff (exponent b a) = star ((complexifyReal f).coeff (exponent a b)) := by
  have hc : cartesianize (conjugateSwap (complexifyReal f)) =
      cartesianize (complexifyReal f) := by
    rw [← cartesianize_conjugateSwap, complexifyReal, cartesianize_complexify]
    ext s
    simp [MvPolynomial.coeff_map]
  have hfix : conjugateSwap (complexifyReal f) = complexifyReal f := by
    simpa [complexify_cartesianize] using congrArg complexify hc
  rw [← coeff_conjugateSwap, hfix]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : f.totalDegree < N)
    (hsym : ∀ z ∈ cartesianLocus f, ζ * z ∈ cartesianLocus f) :
    ∃ m : ℕ, N = 2 * m ∧ rotate ζ (complexifyReal f) = -complexifyReal f ∧
      ∃ A : Polynomial ℂ,
        complexifyReal f = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
          (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
        1 ≤ A.natDegree ∧ A.natDegree ≤ (f.totalDegree - m) / 2 ∧ m + 2 ≤ f.totalDegree := by
  have hirr := complexifyReal_irreducible hf
  have hPdeg := complexifyReal_degree f
  have hPinf : (realLocus (complexifyReal f)).Infinite := by rwa [complexifyReal_locus]
  have hsymP : ∀ z ∈ realLocus (complexifyReal f), ζ * z ∈ realLocus (complexifyReal f) := by
    rw [complexifyReal_locus]
    exact hsym
  rcases rotation_sign_of_realLocus hirr hPinf (hζ.norm'_eq_one (by omega)) hsymP with
    hfix | hanti
  · exfalso
    have hform := irreducible_radial_form hirr
      (fun _ hs => fixed_support hζ (by omega) hfix hs)
    obtain ⟨R, hR, he⟩ := radial_realLocus_is_circle hPinf hform
    exact hnc ⟨0, R, hR, by rw [← complexifyReal_locus]; exact he⟩
  · obtain ⟨m, hm⟩ := anti_even_order hζ hirr.ne_zero hanti
    have hN2 : N = 2 * m := by omega
    have hζ' : IsPrimitiveRoot ζ (2 * m) := hN2 ▸ hζ
    obtain ⟨A, hform, h1, hA, hgap⟩ := irreducible_anti_radial_form (by omega) hζ' hirr
      (by omega) hanti (complexifyReal_conjugate_coeff f)
    exact ⟨m, hN2, hanti, A, hform, h1, hPdeg ▸ hA, hPdeg ▸ hgap⟩
end

#print axioms solution
