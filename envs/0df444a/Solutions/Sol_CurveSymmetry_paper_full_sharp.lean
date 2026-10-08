-- Prove2me | solution 1 for CurveSymmetry.paper_full_sharp
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:57.708601+00:00
-- url     : https://prove2.me/submissions/087515d8-ca15-4132-a1ab-df754656da84

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_direct_euclidean_bound
import Theorems.Thm_CurveSymmetry_exists_cartesian_equation
import Theorems.Thm_CurveSymmetry_fermat_degree
import Theorems.Thm_CurveSymmetry_fermat_direct_card
import Theorems.Thm_CurveSymmetry_fermat_not_circle
import Theorems.Thm_CurveSymmetry_fermat_realLocus_infinite
import Theorems.Thm_CurveSymmetry_isometry_affine_forms
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
lemma direct_coeff_ne_zero {S : Set ℂ} {a b : ℂ} (h : DirectSymmetry S a b) : a ≠ 0 := by
  intro hz
  have hnorm := h.1
  simp [hz] at hnorm
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
/-- The opposite-orientation part is a torsor for the direct part, if nonempty. -/
noncomputable def oppositeDirectEquiv (P : BPoly) (g : OppositeSymmetries P) :
    OppositeSymmetries P ≃ DirectSymmetries P where
  toFun u := ⟨(g.val.1 * star u.val.1, g.val.1 * star u.val.2 + g.val.2),
    opposite_comp_opposite g.prop u.prop⟩
  invFun u := ⟨(g.val.1 * star u.val.1, g.val.1 * star u.val.2 + -g.val.1 * star g.val.2),
    opposite_comp_direct (opposite_inverse g.prop) u.prop⟩
  left_inv u := by
    have hc := mul_star_eq_one_of_norm g.prop.1
    apply Subtype.ext
    apply Prod.ext
    · change g.val.1 * star (g.val.1 * star u.val.1) = u.val.1
      simp only [star_mul, star_star]
      linear_combination u.val.1 * hc
    · change g.val.1 * star (g.val.1 * star u.val.2 + g.val.2) +
        -g.val.1 * star g.val.2 = u.val.2
      simp only [star_add, star_mul, star_star]
      linear_combination u.val.2 * hc
  right_inv u := by
    have hc := mul_star_eq_one_of_norm g.prop.1
    apply Subtype.ext
    apply Prod.ext
    · change g.val.1 * star (g.val.1 * star u.val.1) = u.val.1
      simp only [star_mul, star_star]
      linear_combination u.val.1 * hc
    · change g.val.1 * star (g.val.1 * star u.val.2 + -g.val.1 * star g.val.2) +
        g.val.2 = u.val.2
      simp only [star_add, star_mul, star_star, star_neg]
      linear_combination (u.val.2 - g.val.2) * hc
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
lemma eval_fermat (d : ℕ) (z : ℂ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (fermatPolynomial d) =
      z ^ d + star (z ^ d) - 2 := by
  simp [fermatPolynomial, star_pow]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma fermat_conjugation (d : ℕ) : OppositeSymmetry (realLocus (fermatPolynomial d)) 1 0 := by
  refine ⟨by simp, ?_⟩
  intro z
  simp only [one_mul, add_zero]
  change MvPolynomial.eval _ (fermatPolynomial d) = 0 ↔ MvPolynomial.eval _ (fermatPolynomial d) = 0
  rw [eval_fermat, eval_fermat]
  simp [add_comm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
/-- `Re(z^d) = 1` attains the full Euclidean bound in every degree at least two. -/
theorem fermat_full_card {d : ℕ} (hd : 2 ≤ d) :
    Nat.card (EuclideanSymmetries (fermatPolynomial d)) = 2 * d := by
  have hd' : 0 < d := by omega
  let := (direct_euclidean_bound (fermat_irreducible hd')
    (by rw [fermat_degree hd']; exact hd) (fermat_realLocus_infinite hd') (fermat_not_circle hd')).1
  let g : OppositeSymmetries (fermatPolynomial d) := ⟨(1, 0), fermat_conjugation d⟩
  let : Finite (OppositeSymmetries (fermatPolynomial d)) := Finite.of_injective
    (oppositeDirectEquiv _ g) (oppositeDirectEquiv _ g).injective
  change Nat.card (DirectSymmetries (fermatPolynomial d) ⊕ OppositeSymmetries (fermatPolynomial d)) = _
  rw [Nat.card_sum, Nat.card_congr (oppositeDirectEquiv _ g), fermat_direct_card hd]
  omega
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem full_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (EuclideanSymmetries P) = 2 * d := by
  exact ⟨fermatPolynomial d, fermat_irreducible (by omega), fermat_degree (by omega),
    fermat_realLocus_infinite (by omega), fermat_not_circle (by omega), fermat_full_card hd⟩
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
lemma opposite_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * star z + b = c * star z + d) : (a, b) = (c, d) := by
  apply direct_parameters_unique
  intro z
  simpa using h (star z)
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

namespace CurveSymmetry
set_option autoImplicit false
lemma parametersToIsometry_injective (P : BPoly) : Function.Injective (parametersToIsometry P) := by
  intro u v h
  have he : ∀ z : ℂ, (parametersToIsometry P u).val z = (parametersToIsometry P v).val z :=
    fun z => congrArg (fun f : isometrySymmetryGroup P => f.val z) h
  cases u with
  | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Subtype.ext (direct_parameters_unique he))
      | inr v => exact (direct_ne_opposite (direct_coeff_ne_zero u.prop) he).elim
  | inr u =>
      cases v with
      | inl v => exact (direct_ne_opposite (direct_coeff_ne_zero v.prop) (fun z => (he z).symm)).elim
      | inr v => exact congrArg Sum.inr (Subtype.ext (opposite_parameters_unique he))
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
lemma parametersToIsometry_surjective (P : BPoly) : Function.Surjective (parametersToIsometry P) := by
  intro f
  rcases isometry_affine_forms f.val with ⟨a, b, ha, he⟩ | ⟨a, b, ha, he⟩
  · have hs : DirectSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inl ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm
  · have hs : OppositeSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inr ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable def euclideanIsometryEquiv (P : BPoly) : EuclideanSymmetries P ≃ isometrySymmetryGroup P :=
  Equiv.ofBijective (parametersToIsometry P)
    ⟨parametersToIsometry_injective P, parametersToIsometry_surjective P⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem isometry_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (isometrySymmetryGroup P) = 2 * d := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := full_bound_sharp d hd
  exact ⟨P, hP, hdeg, hinf, hnc, (Nat.card_congr (euclideanIsometryEquiv P)).symm.trans hc⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem cartesian_full_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) = 2 * d := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := isometry_bound_sharp d hd
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl ▸ hinf, ?_, ?_⟩
  · simpa only [NotCircle, hfl] using hnc
  · simpa only [hfl] using hc
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) = 2 * d :=
  cartesian_full_bound_sharp d hd
end

#print axioms solution
