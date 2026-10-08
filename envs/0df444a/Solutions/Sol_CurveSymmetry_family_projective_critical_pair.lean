-- Prove2me | solution 1 for CurveSymmetry.family_projective_critical_pair
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:17.890985+00:00
-- url     : https://prove2.me/submissions/320ddb5a-9902-4c78-83b1-508aadad5e22

-- Solution generated from lean/FamilyGlobalSingularities.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_criticalZero_homogeneousChart
import Theorems.Thm_CurveSymmetry_criticalZero_transport
import Theorems.Thm_CurveSymmetry_family_critical_mixed_iff
import Theorems.Thm_CurveSymmetry_family_projective_critical_swap
import Theorems.Thm_CurveSymmetry_fourTermForm_singular_iff
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
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
open MvPolynomial
lemma fourTermForm_eval (m : ℕ) (a b c d x y : ℂ) :
    planeEval x y (fourTermForm m a b c d) =
      a * x ^ m + b * y ^ m + x * y * (c * x ^ m + d * y ^ m) := by
  simp [fourTermForm, binaryForm]
end CurveSymmetry

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
open MvPolynomial
/-- Both mixed boundary corners are smooth: the indicated partial derivative is `1`. -/
lemma family_mixed_partial (m : ℕ) (hm : 0 < m) (a b : ℂ) :
    planeEval 0 0 (pderiv 1 (familyMixedPolynomial m a b)) = 1 := by
  simp [familyMixedPolynomial, hm.ne']
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_mixed_not_singular {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    ¬ JacobianSingular (familyMixedPolynomial m a b) 0 0 := by
  intro hs
  have he := hs.2.2
  rw [family_mixed_partial m hm] at he
  exact one_ne_zero he
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
lemma familyBihomogeneous_affine (m : ℕ) (α x y : ℂ) :
    familyBihomogeneous m α ![x, 1] ![y, 1] = planeEval x y (familyPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_reciprocal (m : ℕ) (α u v : ℂ) :
    familyBihomogeneous m α ![1, u] ![1, v] =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [familyInfinityPolynomial, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyProjective_infinity_finite {m : ℕ} (hm : 0 < m) (α y : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m α ↔ y = 0 := by
  rw [sphereProjectiveEquiv_infinity, sphereProjectiveEquiv_finite, familyProjective_mk_iff]
  simp [familyBihomogeneous, hm.ne']
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
theorem polynomial_hasFDerivAt {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y => eval y P) (polynomialDifferential P x) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      convert (hasFDerivAt_const (𝕜 := 𝕜) c x) using 1 <;>
        first | rfl | (ext v; simp [polynomialDifferential])
  | add P Q hP hQ =>
      convert hP.add hQ using 1 <;> first | rfl | (ext v; simp [polynomialDifferential, add_mul, Finset.sum_add_distrib])
  | mul_X P i hP =>
      have hi := (ContinuousLinearMap.proj i : (σ → 𝕜) →L[𝕜] 𝕜).hasFDerivAt (x := x)
      convert hP.mul hi using 1 <;> first | rfl | (ext v; simp [polynomialDifferential, pderiv_X,
        Pi.single_apply, apply_ite, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_left_comm])
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem polynomialDifferential_eq_zero_iff {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    polynomialDifferential P x = 0 ↔ ∀ i, eval x (pderiv i P) = 0 := by
  classical
  constructor
  · intro h i
    have hv := congrArg (fun L : (σ → 𝕜) →L[𝕜] 𝕜 => L (Pi.single i 1)) h
    simpa [polynomialDifferential, Pi.single_apply] using hv
  · intro h
    ext v
    simp [polynomialDifferential, h]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem criticalZero_polynomial_iff {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    CriticalZero (fun y => eval y P) x ↔
      eval x P = 0 ∧ ∀ i, eval x (pderiv i P) = 0 := by
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨hz, (polynomialDifferential_eq_zero_iff P x).mp
      ((polynomial_hasFDerivAt P x).unique hd)⟩
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    have he := (polynomialDifferential_eq_zero_iff P x).mpr hd
    simpa only [he] using polynomial_hasFDerivAt P x
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma planeEval_eq_eval (x y : ℂ) (P : BPoly) :
    planeEval x y P = eval ![x, y] P := by
  have he : (fun i : Fin 2 => if i = 0 then x else y) = ![x, y] := by
    ext i
    fin_cases i <;> simp
  simp only [planeEval, he]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The exact bridge to the chart Jacobian predicate used in the earlier local
singularity calculations. -/
theorem jacobianSingular_iff_criticalZero (P : BPoly) (x y : ℂ) :
    JacobianSingular P x y ↔ CriticalZero (fun z => eval z P) ![x, y] := by
  rw [criticalZero_polynomial_iff]
  simp only [JacobianSingular, planeEval_eq_eval, Fin.forall_fin_two]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
/-- The same chart bridge after independent invertible changes in the two
coordinate blocks. In particular this covers all four standard charts. -/
theorem criticalZero_reparametrizedChart (F : HomogeneousPairs → ℂ) (d : ℕ)
    (hscale : ∀ (a b : ℂ) (q : HomogeneousPairs),
      F (a • q.1, b • q.2) = a ^ d * b ^ d * F q)
    (e f : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (v : Fin 2 → ℂ) :
    CriticalZero F (e (homogeneousChart v).1, f (homogeneousChart v).2) ↔
      CriticalZero (fun w => F (e (homogeneousChart w).1, f (homogeneousChart w).2)) v := by
  let T := e.prodCongr f
  have hs (a b : ℂ) (q : HomogeneousPairs) :
      (F ∘ T) (a • q.1, b • q.2) = a ^ d * b ^ d * (F ∘ T) q := by
    simpa [T, Function.comp_def] using hscale a b (T q)
  have he : ∀ q : HomogeneousPairs, F (T q) = 1 * (F ∘ T) q := by simp
  have ht := criticalZero_transport T (F := F ∘ T) (G := F) one_ne_zero he (homogeneousChart v)
  exact ht.trans (criticalZero_homogeneousChart (F ∘ T) d hs v)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
lemma reverseCoordinates_apply (x : Fin 2 → ℂ) :
    reverseCoordinates x = ![x 1, x 0] := by
  ext i
  fin_cases i <;> simp [reverseCoordinates, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
lemma familyBihomogeneous_scale (m : ℕ) (α a b : ℂ) (q : HomogeneousPairs) :
    familyBihomogeneous m α (a • q.1) (b • q.2) =
      a ^ (m + 1) * b ^ (m + 1) * familyBihomogeneous m α q.1 q.2 := by
  rw [familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
theorem family_critical_affine_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![x, 1], ![y, 1]) ↔ JacobianSingular (familyPolynomial m α) x y := by
  have h := criticalZero_homogeneousChart
    (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (m + 1)
    (familyBihomogeneous_scale m α) ![x, y]
  have he : (fun v : Fin 2 → ℂ => familyBihomogeneous m α (homogeneousChart v).1
      (homogeneousChart v).2) = fun v => MvPolynomial.eval v (familyPolynomial m α) := by
    funext v
    rw [homogeneousChart, familyBihomogeneous_affine, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  rw [jacobianSingular_iff_criticalZero]
  simp only [Function.comp_def, he] at h
  convert h using 1
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
theorem family_critical_chart_iff (m : ℕ) (α : ℂ) (P : BPoly)
    (e f : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
    (he : ∀ v : Fin 2 → ℂ,
      familyBihomogeneous m α (e ![v 0, 1]) (f ![v 1, 1]) = MvPolynomial.eval v P)
    (x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (e ![x, 1], f ![y, 1]) ↔ JacobianSingular P x y := by
  have h := criticalZero_reparametrizedChart
    (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (m + 1)
    (familyBihomogeneous_scale m α) e f ![x, y]
  rw [jacobianSingular_iff_criticalZero]
  simp only [homogeneousChart, funext he] at h
  convert h using 1
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
theorem family_critical_reciprocal_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![1, x], ![1, y]) ↔ JacobianSingular (familyInfinityPolynomial m α) x y := by
  have he (v : Fin 2 → ℂ) :
      familyBihomogeneous m α (reverseCoordinates ![v 0, 1])
        (reverseCoordinates ![v 1, 1]) = MvPolynomial.eval v (familyInfinityPolynomial m α) := by
    simp only [reverseCoordinates_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, familyBihomogeneous_reciprocal, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  simpa only [reverseCoordinates_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using family_critical_chart_iff m α _ reverseCoordinates reverseCoordinates he x y
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyProjectiveCritical_subset (m : ℕ) (α : ℂ) :
    familyProjectiveCritical m α ⊆ familyProjectiveCurve m α := fun _ h => h.1
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma family_critical_infinity_finite_false {m : ℕ} (hm : 0 < m) (α y : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (y : Sphere)) ∉
      familyProjectiveCritical m α := by
  intro h
  have hy := (familyProjective_infinity_finite hm α y).mp
    (familyProjectiveCritical_subset m α h)
  subst y
  rw [sphereProjectiveEquiv_infinity, sphereProjectiveEquiv_finite,
    familyProjectiveCritical_mk_iff, family_critical_mixed_iff] at h
  exact family_mixed_not_singular hm α (star α) h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (p q : Sphere) :
    (sphereProjectiveEquiv p, sphereProjectiveEquiv q) ∈ familyProjectiveCritical m α ↔
      (p = (0 : ℂ) ∧ q = (0 : ℂ)) ∨ (p = ∞ ∧ q = ∞) := by
  have hm0 : 0 < m := by omega
  cases p using OnePoint.rec with
  | infty =>
      cases q using OnePoint.rec with
      | infty =>
          rw [sphereProjectiveEquiv_infinity, familyProjectiveCritical_mk_iff,
            family_critical_reciprocal_iff, family_infinity_singular_iff hm ha]
          simp
      | coe y =>
          simp [family_critical_infinity_finite_false hm0 α y]
  | coe x =>
      cases q using OnePoint.rec with
      | infty =>
          have hn : (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∉
              familyProjectiveCritical m α := by
            intro h
            have hs := (family_projective_critical_swap m (star α)
              (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (∞ : Sphere))).mpr
              (by simpa only [star_star] using h)
            exact family_critical_infinity_finite_false hm0 (star α) x hs
          simp [hn]
      | coe y =>
          rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite,
            familyProjectiveCritical_mk_iff, family_critical_affine_iff,
            family_affine_singular_iff hm ha]
          simp
end

#print axioms solution
