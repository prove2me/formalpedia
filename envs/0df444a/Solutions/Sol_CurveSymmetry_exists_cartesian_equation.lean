-- Prove2me | solution 1 for CurveSymmetry.exists_cartesian_equation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:40.910709+00:00
-- url     : https://prove2.me/submissions/6b41014b-3727-4cf8-adf3-7de540b12f67

-- Solution generated from lean/CartesianDescent.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_cartesianize_complexify
import Theorems.Thm_CurveSymmetry_complexify_cartesianize
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_exists_real_equation
import Theorems.Thm_CurveSymmetry_linear_substitution_degree_le
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
lemma realLocus_C_mul {c : ℂ} (hc : c ≠ 0) (P : BPoly) :
    realLocus (C c * P) = realLocus P := by
  ext z
  change eval _ (C c * P) = 0 ↔ eval _ P = 0
  simp [hc]
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
lemma realCoefficients_map {P : BPoly} (hP : map (starRingEnd ℂ) P = P) :
    map Complex.ofRealHom (realCoefficients P) = P := by
  apply (map_mapRange_eq_iff Complex.ofRealHom Complex.re (by simp) P).mpr
  intro s
  have h := congrArg (fun p : BPoly => p.coeff s) hP
  rw [coeff_map] at h
  exact Complex.conj_eq_iff_re.mp h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma conjugateSwap_eq_of_coeff {P : BPoly}
    (hP : ∀ a b : ℕ, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    conjugateSwap P = P := by
  ext s
  have he : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  rw [he, coeff_conjugateSwap, ← hP]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = P.totalDegree ∧
      cartesianLocus f = realLocus P := by
  obtain ⟨s, hs, hreal⟩ := exists_real_equation hP hd hinf
  let Q := C s * P
  have hQ : Irreducible Q := C_mul_irreducible hs hP
  have hfix : conjugateSwap Q = Q := conjugateSwap_eq_of_coeff hreal
  have hmap := realCoefficients_map (by rw [cartesianize_conjugateSwap, hfix])
  let f := realCoefficients (cartesianize Q)
  have he : complexifyReal f = Q := by
    change complexify (map Complex.ofRealHom (realCoefficients (cartesianize Q))) = Q
    rw [hmap, complexify_cartesianize]
  have hf : GeometricallyIrreducible f := by
    change Irreducible (map Complex.ofRealHom (realCoefficients (cartesianize Q)))
    rw [hmap]
    exact hQ.map complexifyEquiv.symm.toMulEquiv
  refine ⟨f, hf, ?_, ?_⟩
  · rw [← complexifyReal_degree, he]
    change (C s * P).totalDegree = P.totalDegree
    rw [totalDegree_mul_of_isDomain (C_ne_zero.mpr hs) hP.ne_zero, totalDegree_C, zero_add]
  · rw [← complexifyReal_locus, he]
    exact realLocus_C_mul hs P
end

#print axioms solution
