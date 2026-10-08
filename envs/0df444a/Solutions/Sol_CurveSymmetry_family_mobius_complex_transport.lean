-- Prove2me | solution 1 for CurveSymmetry.family_mobius_complex_transport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:46.787964+00:00
-- url     : https://prove2.me/submissions/19d6c9c8-cb80-428b-9521-854952ba1a90

-- Solution generated from lean/FamilyGlobalTransport.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_dvd_of_realLocus_subset
import Theorems.Thm_CurveSymmetry_family_bihomogeneous_transport
import Theorems.Thm_CurveSymmetry_family_degreeOf
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_sphereProjectiveEquiv_action
import Theorems.Thm_CurveSymmetry_sphericalFamily_eq
import Theorems.Thm_CurveSymmetry_sphericalFamily_projective_iff
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

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
@[simp] lemma planeEval_C (x y c : ℂ) : planeEval x y (C c) = c := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_zero (x y : ℂ) : planeEval x y (X 0) = x := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_one (x y : ℂ) : planeEval x y (X 1) = y := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma sphereProjectiveEquiv_finite (z : ℂ) :
    sphereProjectiveEquiv (z : Sphere) = Projectivization.mk ℂ ![z, 1] (by simp) := rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
theorem finite_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    (z : Sphere) ∈ sphericalFamily m α ↔ z ∈ extremalCurve m α := by
  rw [sphericalFamily_eq hm ha]
  simp only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
    Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_smul_left (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α (a • x) y = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_smul_right (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α x (a • y) = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem familyProjective_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ familyProjectiveCurve m α ↔
      familyBihomogeneous m α x y = 0 := by
  change familyBihomogeneous m α (Projectivization.mk ℂ x hx).rep
    (Projectivization.mk ℂ y hy).rep = 0 ↔ _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  simp [Units.smul_def, familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem sphereRealDiagonal_action (g : MobiusMatrix) (p : Sphere) :
    sphereRealDiagonal (g • p) = complexifiedMobius g (sphereRealDiagonal p) := by
  apply Prod.ext
  · exact sphereProjectiveEquiv_action g p
  · change sphereProjectiveEquiv (OnePoint.map (starRingEnd ℂ) (g • p)) =
      (g.map (starRingEnd ℂ)) • sphereProjectiveEquiv (OnePoint.map (starRingEnd ℂ) p)
    rw [OnePoint.map_smul, sphereProjectiveEquiv_action]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma familyMobiusPullback_eval (m : ℕ) (β x y : ℂ) (g : MobiusMatrix) :
    planeEval x y (familyMobiusPullback m β g) =
      familyBihomogeneous m β (g • ![x, 1]) ((g.map (starRingEnd ℂ)) • ![y, 1]) := by
  simp [familyMobiusPullback, mobiusX, mobiusY, familyBihomogeneous,
    Matrix.GeneralLinearGroup.fin_two_smul]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem familyMobiusPullback_projective_iff (m : ℕ) (β x y : ℂ) (g : MobiusMatrix) :
    complexifiedMobius g (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m β ↔ planeEval x y (familyMobiusPullback m β g) = 0 := by
  change (g • sphereProjectiveEquiv (x : Sphere),
    (g.map (starRingEnd ℂ)) • sphereProjectiveEquiv (y : Sphere)) ∈ _ ↔ _
  rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite,
    Projectivization.smul_mk, Projectivization.smul_mk, familyProjective_mk_iff,
    familyMobiusPullback_eval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Spherical real-locus inclusion already forces divisibility by the source
equation, even when the matrix has poles on the curve. Nonzero scalar
proportionality and singularity transport are still separate obligations. -/
theorem family_dvd_mobiusPullback {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    familyPolynomial m α ∣ familyMobiusPullback m β g := by
  apply dvd_of_realLocus_subset (familyPolynomial_irreducible hm ha)
    (family_realLocus_infinite hm ha)
  intro z hz
  have hzSphere : (z : Sphere) ∈ sphericalFamily m α := by
    rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
    exact hz
  have ht := (sphericalFamily_projective_iff hm hb (g • (z : Sphere))).mpr
    (hmap (z : Sphere) hzSphere)
  rw [sphereRealDiagonal_action] at ht
  change planeEval z (star z) (familyMobiusPullback m β g) = 0
  exact (familyMobiusPullback_projective_iff m β z (star z) g).mp ht
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_add_bound (i : Fin 2) {p q : BPoly} {n : ℕ}
    (hp : p.degreeOf i ≤ n) (hq : q.degreeOf i ≤ n) : (p + q).degreeOf i ≤ n :=
  (degreeOf_add_le i p q).trans (max_le hp hq)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_mul_bound (i : Fin 2) {p q : BPoly} {a b : ℕ}
    (hp : p.degreeOf i ≤ a) (hq : q.degreeOf i ≤ b) : (p * q).degreeOf i ≤ a + b :=
  (degreeOf_mul_le i p q).trans (Nat.add_le_add hp hq)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_pow_bound (i : Fin 2) {p : BPoly} {a : ℕ}
    (hp : p.degreeOf i ≤ a) (n : ℕ) : (p ^ n).degreeOf i ≤ n * a :=
  (degreeOf_pow_le i p n).trans (Nat.mul_le_mul_left n hp)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_affine_bound (i j : Fin 2) (a b : ℂ) :
    (C a * X j + C b : BPoly).degreeOf i ≤ if i = j then 1 else 0 := by
  calc
    _ ≤ max ((C a * X j : BPoly).degreeOf i) ((C b : BPoly).degreeOf i) :=
      degreeOf_add_le i _ _
    _ ≤ max ((X j : BPoly).degreeOf i) 0 :=
      max_le_max (degreeOf_C_mul_le _ i a) (by simp)
    _ = _ := by simp [degreeOf_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma biform_degree_bound (i : Fin 2) (m : ℕ) (β : ℂ)
    (u v s t : BPoly) {a b : ℕ} (hu : u.degreeOf i ≤ a) (hv : v.degreeOf i ≤ a)
    (hs : s.degreeOf i ≤ b) (ht : t.degreeOf i ≤ b) :
    (C β * u ^ m * v * t ^ (m + 1) + u ^ (m + 1) * s * t ^ m +
      C (star β) * v ^ (m + 1) * s ^ m * t + u * v ^ m * s ^ (m + 1)).degreeOf i ≤
        (m + 1) * (a + b) := by
  apply degree_add_bound i (degree_add_bound i (degree_add_bound i ?_ ?_) ?_) ?_
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i β).trans (degree_pow_bound i hu m)) hv)
      (degree_pow_bound i ht (m + 1))
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i (degree_pow_bound i hu (m + 1)) hs)
      (degree_pow_bound i ht m)
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i (star β)).trans (degree_pow_bound i hv (m + 1)))
      (degree_pow_bound i hs m)) ht
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i hu (degree_pow_bound i hv m))
      (degree_pow_bound i hs (m + 1))
    convert h using 1
    ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
/-- Arbitrary product-projective pullback never exceeds degree `m+1` in either
affine variable. The total degree can be larger than the source total degree. -/
theorem familyMobiusPullback_degreeOf_le (m : ℕ) (β : ℂ) (g : MobiusMatrix) (i : Fin 2) :
    (familyMobiusPullback m β g).degreeOf i ≤ m + 1 := by
  have h := biform_degree_bound i m β (mobiusX g 0) (mobiusX g 1) (mobiusY g 0) (mobiusY g 1)
    (degree_affine_bound i 0 (g 0 0) (g 0 1))
    (degree_affine_bound i 0 (g 1 0) (g 1 1))
    (degree_affine_bound i 1 (star (g 0 0)) (star (g 0 1)))
    (degree_affine_bound i 1 (star (g 1 0)) (star (g 1 1)))
  fin_cases i <;> simpa [familyMobiusPullback] using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma constant_of_degreeOf_zero {S : BPoly} (h : ∀ i, S.degreeOf i = 0) :
    S = C (S.coeff 0) := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · have hs : d ∉ S.support := by
      intro hs
      apply hd
      ext i
      have hi := monomial_le_degreeOf i hs
      simpa [h i] using Nat.eq_zero_of_le_zero (by simpa [h i] using hi)
    have hc : S.coeff d = 0 := by simpa only [mem_support_iff, not_not] using hs
    rw [hc, coeff_C_of_ne_zero hd]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
/-- Separate degree bounds, not a total-degree shortcut, remove the extra factor. -/
theorem proportional_of_family_dvd {m : ℕ} (hm : 0 < m) (α : ℂ) {Q : BPoly}
    (hQ : Q ≠ 0) (hdiv : familyPolynomial m α ∣ Q)
    (hdeg : ∀ i, Q.degreeOf i ≤ m + 1) :
    ∃ c : ℂ, c ≠ 0 ∧ Q = C c * familyPolynomial m α := by
  have hP : familyPolynomial m α ≠ 0 := by
    apply ne_zero_of_degreeOf_ne_zero (i := 0)
    rw [family_degreeOf hm]
    omega
  obtain ⟨S, hS⟩ := hdiv
  have hs0 : S ≠ 0 := by intro h; apply hQ; simp [hS, h]
  have hsdeg : ∀ i, S.degreeOf i = 0 := by
    intro i
    have hmul := degreeOf_mul_eq (n := i) hP hs0
    rw [← hS, family_degreeOf hm] at hmul
    have hi := hdeg i
    omega
  have hcS := constant_of_degreeOf_zero hsdeg
  refine ⟨S.coeff 0, ?_, ?_⟩
  · intro hc
    exact hs0 (by simpa [hc] using hcS)
  · rw [hS, hcS, mul_comm]
    simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma positive_real_mem_family_iff (m : ℕ) (β : ℂ) {r : ℝ} (hr : 0 < r) :
    (r : ℂ) ∈ extremalCurve m β ↔ r ^ 2 + β.re = 0 := by
  simp [extremalCurve, ← Complex.ofReal_pow, Complex.norm_real, abs_of_pos hr,
    pow_ne_zero m (ne_of_gt hr)]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
lemma sphericalFamily_ne_univ {m : ℕ} (hm : 0 < m) {β : ℂ} (hb : β ≠ star β) :
    sphericalFamily m β ≠ Set.univ := by
  intro he
  have h1 : (((1 : ℝ) : ℂ) : Sphere) ∈ sphericalFamily m β := by rw [he]; trivial
  have h2 : (((2 : ℝ) : ℂ) : Sphere) ∈ sphericalFamily m β := by rw [he]; trivial
  rw [finite_mem_sphericalFamily_iff hm hb, positive_real_mem_family_iff m β (by norm_num)] at h1 h2
  norm_num at h1 h2
  linarith
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
/-- The cleared pullback is nonzero even when the matrix moves infinity.
If it vanished identically, the closed target would contain the complement
of one sphere point, hence the whole sphere, a contradiction. -/
theorem familyMobiusPullback_ne_zero {m : ℕ} (hm : 0 < m) {β : ℂ}
    (hb : β ≠ star β) (g : MobiusMatrix) : familyMobiusPullback m β g ≠ 0 := by
  intro hz
  have hfinite : ∀ z : ℂ, g • (z : Sphere) ∈ sphericalFamily m β := by
    intro z
    apply (sphericalFamily_projective_iff hm hb _).mp
    rw [sphereRealDiagonal_action]
    apply (familyMobiusPullback_projective_iff m β z (star z) g).mpr
    simp [hz]
  have hsub : ({g • (∞ : Sphere)} : Set Sphere)ᶜ ⊆ sphericalFamily m β := by
    intro p hp
    obtain ⟨q, hq⟩ := (MulAction.toPerm g).surjective p
    change g • q = p at hq
    subst p
    cases q using OnePoint.rec with
    | infty => exact (hp rfl).elim
    | coe z => exact hfinite z
  have hdense : Dense (({g • (∞ : Sphere)} : Set Sphere)ᶜ) := dense_compl_singleton _
  apply sphericalFamily_ne_univ hm hb
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← hdense.closure_eq]
  exact closure_minimal hsub isClosed_closure
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
/-- Arbitrary Möbius inclusion of the actual spherical loci gives a nonzero
scalar polynomial identity. No pair preservation or normal map form is assumed. -/
theorem family_mobius_proportional {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    ∃ c : ℂ, c ≠ 0 ∧ familyMobiusPullback m β g = C c * familyPolynomial m α :=
  proportional_of_family_dvd hm α (familyMobiusPullback_ne_zero hm hb g)
    (family_dvd_mobiusPullback hm ha hb g hmap) (familyMobiusPullback_degreeOf_le m β g)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The nonzero polynomial identity transports the entire product-projective
zero locus, including every boundary chart, in both directions. -/
theorem family_projective_transport_of_identity {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (hk : k ≠ 0) (he : familyMobiusPullback m β g = C k * familyPolynomial m α)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  rcases p with ⟨p, q⟩
  induction p using Projectivization.ind with | h x hx =>
  induction q using Projectivization.ind with | h y hy =>
  change (g • Projectivization.mk ℂ x hx,
    (g.map (starRingEnd ℂ)) • Projectivization.mk ℂ y hy) ∈ _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.smul_mk,
    familyProjective_mk_iff, familyProjective_mk_iff, family_bihomogeneous_transport he]
  simp [hk]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  obtain ⟨k, hk, he⟩ := family_mobius_proportional hm ha hb g hmap
  exact family_projective_transport_of_identity hk he p
end

#print axioms solution
