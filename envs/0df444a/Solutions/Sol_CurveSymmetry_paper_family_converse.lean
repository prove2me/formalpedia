-- Prove2me | solution 1 for CurveSymmetry.paper_family_converse
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:56.981854+00:00
-- url     : https://prove2.me/submissions/8019e8c3-713a-4c8c-9abb-5689d2609675

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_exists_cartesian_equation
import Theorems.Thm_CurveSymmetry_family_direct_card
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
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

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 3 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = m + 2 ∧
      cartesianLocus f = extremalCurve m α ∧ (cartesianLocus f).Infinite ∧
      (¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) = 2 * m := by
  have hP := familyPolynomial_irreducible (by omega : 0 < m) ha
  have hdeg := family_degree (by omega : 0 < m) α
  have hinf := family_realLocus_infinite (by omega : 0 < m) ha
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  refine ⟨f, hf, hfd.trans hdeg, hfl.trans (family_locus_eq m α), hfl ▸ hinf, ?_, ?_⟩
  · simpa only [hfl, NotCircle] using family_not_circle (by omega : 0 < m) ha
  · rw [hfl, ← Nat.card_congr (directIsometryEquiv (familyPolynomial m α))]
    exact family_direct_card (by omega) ha
end

#print axioms solution
