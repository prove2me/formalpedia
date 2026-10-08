-- Prove2me | solution 1 for CurveSymmetry.family_ordinary_multiple_points
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:33.224022+00:00
-- url     : https://prove2.me/submissions/db4368ed-5a99-4e14-b520-7492a969f67a

-- Solution generated from lean/OrdinaryMultiplePoints.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Theorems.Thm_CurveSymmetry_criticalZero_transport
import Theorems.Thm_CurveSymmetry_family_critical_mixed_iff
import Theorems.Thm_CurveSymmetry_family_projective_critical_eq_pair
import Theorems.Thm_CurveSymmetry_fourTermForm_singular_iff
import Theorems.Thm_CurveSymmetry_fourTermForm_tangent_data
import Theorems.Thm_CurveSymmetry_mem_pointIdeal_iff
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The only affine singular point of the extremal family is `(0,0)`. -/
theorem family_affine_singular_iff {m : ℕ} (hm : 2 ≤ m) {α x y : ℂ} (ha : α ≠ star α) :
    JacobianSingular (familyPolynomial m α) x y ↔ x = 0 ∧ y = 0 := by
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  rw [family_fourTerm]
  apply fourTermForm_singular_iff hm ha0 (star_ne_zero.mpr ha0)
  simpa using sub_ne_zero.mpr ha
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_infinity_singular_iff {m : ℕ} (hm : 2 ≤ m) {α u v : ℂ} (ha : α ≠ star α) :
    JacobianSingular (familyInfinityPolynomial m α) u v ↔ u = 0 ∧ v = 0 := by
  apply fourTermForm_singular_iff hm one_ne_zero one_ne_zero
  simpa using sub_ne_zero.mpr ha
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
lemma sphereProjectiveEquiv_infinity :
    sphereProjectiveEquiv (∞ : Sphere) = Projectivization.mk ℂ ![1, 0] (by simp) := rfl
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
/-- Independent nonzero rescaling of either homogeneous block does not change
the condition. This supplies representative independence on `P¹ × P¹`. -/
theorem family_homogeneous_critical_smul (m : ℕ) (α : ℂ) (a b : ℂˣ)
    (p : HomogeneousPairs) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (a • p.1, b • p.2) ↔
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) p := by
  let T : HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
    ((DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) a).prodCongr
      (DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) b)).toContinuousLinearEquiv
  apply criticalZero_transport T (k := (a : ℂ) ^ (m + 1) * (b : ℂ) ^ (m + 1))
  · exact mul_ne_zero (pow_ne_zero _ a.ne_zero) (pow_ne_zero _ b.ne_zero)
  · intro q
    change familyBihomogeneous m α (a • q.1) (b • q.2) = _
    simp only [Units.smul_def, familyBihomogeneous_smul_left,
      familyBihomogeneous_smul_right]
    ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
theorem familyProjectiveCritical_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈
      familyProjectiveCritical m α ↔
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (x, y) := by
  simp only [familyProjectiveCritical, Set.mem_ofPred_eq]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  exact family_homogeneous_critical_smul m α a b (x, y)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma pointIdeal_origin : pointIdeal 0 0 = idealOfVars (Fin 2) ℂ := by
  have hr : Set.range (X : Fin 2 → BPoly) = {X 0, X 1} := by
    ext p
    simp [Fin.exists_fin_two, eq_comm]
  simp [pointIdeal, idealOfVars, hr]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The polynomials whose value and both formal partial derivatives vanish at a
point form an ideal. -/
noncomputable def jacobianIdeal (x y : ℂ) : Ideal BPoly where
  carrier := {P | JacobianSingular P x y}
  add_mem' := by
    rintro P Q ⟨hP, hP0, hP1⟩ ⟨hQ, hQ0, hQ1⟩
    exact ⟨by simp [hP, hQ], by simp [hP0, hQ0], by simp [hP1, hQ1]⟩
  zero_mem' := by simp [JacobianSingular]
  smul_mem' := by
    rintro c P ⟨hP, hP0, hP1⟩
    exact ⟨by simp [hP], by simp [hP, hP0], by simp [hP, hP1]⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A second-order zero is a Jacobian singularity. -/
theorem jacobianSingular_of_mem_sq {P : BPoly} {x y : ℂ}
    (hP : P ∈ pointIdeal x y ^ 2) : JacobianSingular P x y := by
  have hle : pointIdeal x y ^ 2 ≤ jacobianIdeal x y := by
    rw [sq, Ideal.mul_le]
    intro r hr s hs
    have hr0 := (mem_pointIdeal_iff r x y).mp hr
    have hs0 := (mem_pointIdeal_iff s x y).mp hs
    exact ⟨by simp [hr0, hs0], by simp [hr0, hs0], by simp [hr0, hs0]⟩
  exact hle hP
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- A nonsingular zero of a plane equation has multiplicity exactly one. -/
theorem hasMultiplicityAt_one {P : BPoly} {x y : ℂ} (hz : planeEval x y P = 0)
    (hs : ¬ JacobianSingular P x y) : HasMultiplicityAt P x y 1 :=
  ⟨by simpa using (mem_pointIdeal_iff P x y).mpr hz,
    fun h => hs (jacobianSingular_of_mem_sq h)⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma homogeneousComponent_eq_zero_of_mem_pow {P : BPoly} {n : ℕ}
    (hP : P ∈ idealOfVars (Fin 2) ℂ ^ (n + 1)) : homogeneousComponent n P = 0 := by
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero]
  split_ifs with hd
  · exact (mem_pow_idealOfVars_iff' (n + 1) P).mp hP d (by omega)
  · rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The binary tangent form splits into `m` explicit distinct linear factors. -/
theorem binaryForm_eq_prod {m : ℕ} (hm : 0 < m) {a b w ζ : ℂ} (ha : a ≠ 0)
    (hζ : IsPrimitiveRoot ζ m) (hw : w ^ m = -b / a) :
    binaryForm m a b =
      C a * ∏ i : Fin m, (C (1 : ℂ) * X 0 + C (-(ζ ^ (i : ℕ) * w)) * X 1) := by
  have hpoly := _root_.X_pow_sub_C_eq_prod hζ hm hw
  apply MvPolynomial.funext
  intro v
  have hprod : ∀ t : ℂ, t ^ m - (-b / a) = ∏ i ∈ Finset.range m, (t - ζ ^ i * w) := by
    intro t
    simpa [Polynomial.eval_prod] using congrArg (Polynomial.eval t) hpoly
  simp only [binaryForm, map_add, map_mul, map_pow, eval_C, eval_X, map_prod, map_neg,
    one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => v 0 + -(ζ ^ i * w) * v 1) m]
  by_cases hv : v 1 = 0
  · simp [hv, hm.ne']
  · have hs : ∏ i ∈ Finset.range m, (v 0 + -(ζ ^ i * w) * v 1) =
        v 1 ^ m * ∏ i ∈ Finset.range m, (v 0 / v 1 - ζ ^ i * w) := by
      rw [← Finset.card_range m, ← Finset.prod_const, Finset.card_range,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      field_simp
      ring
    have hab : a * (-b / a) = -b := by field_simp
    rw [hs, ← hprod, div_pow, mul_sub, mul_div_cancel₀ _ (pow_ne_zero m hv)]
    linear_combination (v 1 ^ m) * hab
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The four-term chart equation has an ordinary `m`-fold point at its origin. -/
theorem fourTermForm_ordinary {m : ℕ} (hm : 0 < m) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (c d : ℂ) : OrdinaryAtOrigin (fourTermForm m a b c d) m := by
  obtain ⟨hlow, hcomp, hnz, _⟩ := fourTermForm_tangent_data hm ha hb c d
  have hbin (a b : ℂ) : binaryForm m a b ∈ idealOfVars (Fin 2) ℂ ^ m := by
    have hX (i : Fin 2) : (X i : BPoly) ^ m ∈ idealOfVars (Fin 2) ℂ ^ m :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) m
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hX 0)) (Ideal.mul_mem_left _ _ (hX 1))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pointIdeal_origin]
    exact Ideal.add_mem _ (hbin a b) (Ideal.mul_mem_left _ _ (hbin c d))
  · rw [pointIdeal_origin]
    intro hmem
    exact hnz (hcomp ▸ homogeneousComponent_eq_zero_of_mem_pow hmem)
  · let ζ := Complex.exp (2 * Real.pi * Complex.I / m)
    have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) hm
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact div_ne_zero (neg_ne_zero.mpr hb) ha (by simpa [hm.ne'] using hw.symm)
    refine ⟨a, fun i => ![1, -(ζ ^ (i : ℕ) * w)], ha, fun i => by simp, ?_, ?_⟩
    · intro i j hij
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hpow : ζ ^ (i : ℕ) ≠ ζ ^ (j : ℕ) := by
        intro he
        exact hij (Fin.ext (hζ.pow_inj i.isLt j.isLt he))
      have hsub : ζ ^ (i : ℕ) - ζ ^ (j : ℕ) ≠ 0 := sub_ne_zero.mpr hpow
      intro hz
      apply mul_ne_zero hsub hw0
      linear_combination hz
    · rw [hcomp, binaryForm_eq_prod hm ha hζ hw]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma projective_mk_one_ne_origin (x : ℂ) :
    Projectivization.mk ℂ ![1, x] (by simp) ≠ sphereProjectiveEquiv ((0 : ℂ) : Sphere) := by
  intro h
  rw [sphereProjectiveEquiv_finite, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h := congrFun ha 0
  simp at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma projective_mk_one_ne_infinity (y : ℂ) :
    Projectivization.mk ℂ ![y, 1] (by simp) ≠ sphereProjectiveEquiv (OnePoint.infty : Sphere) := by
  intro h
  rw [sphereProjectiveEquiv_infinity, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h := congrFun ha 1
  simp at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The first mixed chart equation has no Jacobian singularity anywhere. -/
theorem family_mixed_chart_nonsingular {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α)
    (x y : ℂ) : ¬ JacobianSingular (familyMixedPolynomial m α (star α)) x y := by
  intro hs
  have hmem := (familyProjectiveCritical_mk_iff m α ![1, x] ![y, 1] (by simp) (by simp)).mpr
    ((family_critical_mixed_iff m α x y).mpr hs)
  rw [family_projective_critical_eq_pair hm ha] at hmem
  rcases hmem with h | h
  · exact projective_mk_one_ne_origin x (Prod.mk.inj h).1
  · exact projective_mk_one_ne_infinity y (Prod.mk.inj (Set.mem_singleton_iff.mp h)).2
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    OrdinaryAtOrigin (familyPolynomial m α) m ∧
      OrdinaryAtOrigin (familyInfinityPolynomial m α) m ∧
      (∀ x y : ℂ, planeEval x y (familyPolynomial m α) = 0 → ¬ (x = 0 ∧ y = 0) →
        HasMultiplicityAt (familyPolynomial m α) x y 1) ∧
      (∀ u v : ℂ, planeEval u v (familyInfinityPolynomial m α) = 0 → ¬ (u = 0 ∧ v = 0) →
        HasMultiplicityAt (familyInfinityPolynomial m α) u v 1) ∧
      (∀ u y : ℂ, planeEval u y (familyMixedPolynomial m α (star α)) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m α (star α)) u y 1) ∧
      (∀ v x : ℂ, planeEval v x (familyMixedPolynomial m (star α) α) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m (star α) α) v x 1) := by
  have hm0 : 0 < m := by omega
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [family_fourTerm]
    exact fourTermForm_ordinary hm0 ha0 (star_ne_zero.mpr ha0) 1 1
  · exact fourTermForm_ordinary hm0 one_ne_zero one_ne_zero (star α) α
  · intro x y hz hne
    exact hasMultiplicityAt_one hz (fun hs => hne ((family_affine_singular_iff hm ha).mp hs))
  · intro u v hz hne
    exact hasMultiplicityAt_one hz (fun hs => hne ((family_infinity_singular_iff hm ha).mp hs))
  · intro u y hz
    exact hasMultiplicityAt_one hz (family_mixed_chart_nonsingular hm ha u y)
  · intro v x hz
    have hs := family_mixed_chart_nonsingular hm has v x
    rw [star_star] at hs
    exact hasMultiplicityAt_one hz hs
end

#print axioms solution
