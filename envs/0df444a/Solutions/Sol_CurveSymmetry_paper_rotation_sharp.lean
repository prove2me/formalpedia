-- Prove2me | solution 1 for CurveSymmetry.paper_rotation_sharp
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:59.003995+00:00
-- url     : https://prove2.me/submissions/7a80a318-f0ce-455e-8bb3-d0d09efbc329

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_exists_cartesian_equation
import Theorems.Thm_CurveSymmetry_family_direct_card
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_fermat_degree
import Theorems.Thm_CurveSymmetry_fermat_direct_card
import Theorems.Thm_CurveSymmetry_fermat_not_circle
import Theorems.Thm_CurveSymmetry_fermat_realLocus_infinite
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
theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_not_circle {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    NotCircle (familyPolynomial m α) := by
  rintro ⟨c, R, hR, he⟩
  obtain ⟨z, hz, hn⟩ := family_point_of_norm hm ha
    (show 0 ≤ ‖c‖ + R + 1 by positivity)
  rw [he, Metric.mem_sphere, dist_eq_norm] at hz
  have hb := norm_add_le (z - c) c
  rw [sub_add_cancel, hz, hn] at hb
  linarith
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
/-- The exact maximum direct-symmetry count is attained in every degree. -/
theorem rotation_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (DirectSymmetries P) = max d (2 * d - 4) := by
  by_cases hsmall : d < 4
  · refine ⟨fermatPolynomial d, fermat_irreducible (by omega), fermat_degree (by omega),
      fermat_realLocus_infinite (by omega), fermat_not_circle (by omega), ?_⟩
    rw [fermat_direct_card hd]
    omega
  · have hm : 2 ≤ d - 2 := by omega
    have hm' : 0 < d - 2 := by omega
    have hI : Complex.I ≠ star Complex.I := by
      intro h
      have he := congrArg Complex.im h
      norm_num at he
    refine ⟨familyPolynomial (d - 2) Complex.I, familyPolynomial_irreducible hm' hI,
      ?_, family_realLocus_infinite hm' hI, family_not_circle hm' hI, ?_⟩
    · rw [family_degree hm']; omega
    · rw [family_direct_card hm hI]; omega
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
/-- Sharpness is attained by real Cartesian polynomials in every degree. -/
theorem cartesian_rotation_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (CartesianDirectSymmetries f) = max d (2 * d - 4) := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := rotation_bound_sharp d hd
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl ▸ hinf, ?_, ?_⟩
  · simpa only [NotCircle, hfl] using hnc
  · simpa only [CartesianDirectSymmetries, hfl] using hc
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
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = d ∧
      (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) = max d (2 * d - 4) := by
  obtain ⟨f, hf, hdeg, hinf, hnc, hc⟩ := cartesian_rotation_bound_sharp d hd
  exact ⟨f, hf, hdeg, hinf, hnc, (cartesian_direct_card f).symm.trans hc⟩
end

#print axioms solution
