-- Prove2me | solution 1 for CurveSymmetry.paper_sharp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:37.933097+00:00
-- url     : https://prove2.me/submissions/ce47bc2e-159a-48c9-b409-d244d8bdcd99

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_cartesianize_complexify
import Theorems.Thm_CurveSymmetry_complexify_cartesianize
import Theorems.Thm_CurveSymmetry_direct_bound_with_opposite
import Theorems.Thm_CurveSymmetry_direct_euclidean_bound
import Theorems.Thm_CurveSymmetry_direct_symmetries_common_center
import Theorems.Thm_CurveSymmetry_eval_complexify
import Theorems.Thm_CurveSymmetry_isometry_affine_forms
import Theorems.Thm_CurveSymmetry_linear_substitution_degree_le
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
open MvPolynomial
/-- The complete Euclidean group is finite and has at most twice the degree.
This proves the upper bound, not its sharpness or the equality classification. -/
theorem full_euclidean_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (EuclideanSymmetries P) ∧ Nat.card (EuclideanSymmetries P) ≤ 2 * P.totalDegree := by
  classical
  obtain ⟨hf, hb⟩ := direct_euclidean_bound hP hd hinf hcircle
  let := hf
  by_cases hex : Nonempty (OppositeSymmetries P)
  · let g := Classical.choice hex
    let : Finite (OppositeSymmetries P) := Finite.of_injective
      (oppositeDirectEquiv P g) (oppositeDirectEquiv P g).injective
    refine ⟨inferInstance, ?_⟩
    change Nat.card (DirectSymmetries P ⊕ OppositeSymmetries P) ≤ _
    rw [Nat.card_sum, Nat.card_congr (oppositeDirectEquiv P g)]
    have h := direct_bound_with_opposite hP hd hinf hcircle g
    omega
  · let : IsEmpty (OppositeSymmetries P) := not_nonempty_iff.mp hex
    refine ⟨inferInstance, ?_⟩
    change Nat.card (DirectSymmetries P ⊕ OppositeSymmetries P) ≤ _
    rw [Nat.card_sum, Nat.card_of_isEmpty (α := OppositeSymmetries P)]
    omega
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
/-- The full bound for the actual subgroup of Mathlib Euclidean isometries. -/
theorem isometry_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (isometrySymmetryGroup P) ∧ Nat.card (isometrySymmetryGroup P) ≤ 2 * P.totalDegree := by
  obtain ⟨hf, hb⟩ := full_euclidean_bound hP hd hinf hcircle
  let := hf
  refine ⟨Finite.of_equiv _ (euclideanIsometryEquiv P), ?_⟩
  rwa [← Nat.card_congr (euclideanIsometryEquiv P)]
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
/-- The full bound for the actual Euclidean-isometry subgroup of a Cartesian zero set. -/
theorem cartesian_isometry_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (isometrySetGroup (cartesianLocus f)) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) ≤ 2 * f.totalDegree := by
  have h := isometry_group_bound (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
  simpa only [isometrySymmetryGroup, complexifyReal_locus, complexifyReal_degree] using h
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
lemma directSlope_injective {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    Function.Injective (directSlope (realLocus P)) := by
  obtain ⟨t, ht⟩ := direct_symmetries_common_center hP hd hinf.nonempty
  intro f g he
  obtain ⟨a, b, ha, hf⟩ := f.prop.2
  obtain ⟨c, d, hc, hg⟩ := g.prop.2
  have hab : DirectSymmetry (realLocus P) a b :=
    ⟨ha, fun z => by rw [← hf]; exact f.prop.1 z⟩
  have hcd : DirectSymmetry (realLocus P) c d :=
    ⟨hc, fun z => by rw [← hg]; exact g.prop.1 z⟩
  change f.val 1 - f.val 0 = g.val 1 - g.val 0 at he
  rw [hf, hf, hg, hg] at he
  have hac : a = c := by linear_combination he
  have hbd : b = d := by rw [ht a b hab, ht c d hcd, hac]
  apply Subtype.ext
  apply IsometryEquiv.ext
  intro z
  rw [hf, hg, hac, hbd]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
/-- The actual direct-isometry subgroup is finite, cyclic, and obeys the sharp bound. -/
theorem direct_isometry_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hnc : NotCircle P) :
    Finite (directIsometryGroup (realLocus P)) ∧ IsCyclic (directIsometryGroup (realLocus P)) ∧
      Nat.card (directIsometryGroup (realLocus P)) ≤ max P.totalDegree (2 * P.totalDegree - 4) := by
  obtain ⟨hf, hb⟩ := direct_euclidean_bound hP hd hinf hnc
  let := hf
  let := Finite.of_equiv _ (directIsometryEquiv P)
  refine ⟨inferInstance, isCyclic_of_injective_ringHom _ (directSlope_injective hP hd hinf), ?_⟩
  rwa [← Nat.card_congr (directIsometryEquiv P)]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem cartesian_direct_isometry_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (directIsometryGroup (cartesianLocus f)) ∧
      IsCyclic (directIsometryGroup (cartesianLocus f)) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) ≤ max f.totalDegree (2 * f.totalDegree - 4) := by
  have h := direct_isometry_group_bound (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
  rw [complexifyReal_locus, complexifyReal_degree] at h
  exact h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (isometrySetGroup (cartesianLocus f)) ∧
      Finite (directIsometryGroup (cartesianLocus f)) ∧
      IsCyclic (directIsometryGroup (cartesianLocus f)) ∧
      Nat.card (directIsometryGroup (cartesianLocus f)) ≤ max f.totalDegree (2 * f.totalDegree - 4) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) ≤ 2 * f.totalDegree := by
  obtain ⟨hfull, hbfull⟩ := cartesian_isometry_bound hf hd hinf hnc
  obtain ⟨hdir, hcyc, hbdir⟩ := cartesian_direct_isometry_bound hf hd hinf hnc
  exact ⟨hfull, hdir, hcyc, hbdir, hbfull⟩
end

#print axioms solution
