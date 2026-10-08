-- Prove2me | solution 1 for CurveSymmetry.paper_isometry_sign
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:58.357443+00:00
-- url     : https://prove2.me/submissions/54651778-ca34-4379-a0fe-1a481f4ee569

-- Solution generated from lean/IsometrySign.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_cartesianize_complexify
import Theorems.Thm_CurveSymmetry_complexify_cartesianize
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_isometry_sign_of_realLocus
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
lemma eval_complexifyReal (f : RPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (complexifyReal f) =
      (eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f : ℂ) := by
  change eval _ (complexify (map Complex.ofRealHom f)) = _
  rw [eval_complexify, eval_real_map]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (T : isometrySetGroup (cartesianLocus f)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then (T.val z).re else (T.val z).im) f =
        ε * eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by
  have hT : T.val ∈ isometrySymmetryGroup (complexifyReal f) := by
    rw [isometrySymmetryGroup, complexifyReal_locus]
    exact T.prop
  obtain ⟨ε, hε, hid, hopp⟩ := isometry_sign_of_realLocus (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus]) ⟨T.val, hT⟩
  rcases hε with rfl | rfl
  · refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
    have h := hid z
    rw [eval_complexifyReal, eval_complexifyReal] at h
    exact_mod_cast h
  · refine ⟨-1, Or.inr rfl, fun z => ?_, fun h => ?_⟩
    · have h := hid z
      rw [eval_complexifyReal, eval_complexifyReal] at h
      exact_mod_cast h
    · have h1 := hopp h
      norm_num at h1
end

#print axioms solution
