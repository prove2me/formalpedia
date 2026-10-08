-- Prove2me | solution 1 for CurveSymmetry.family_critical_mixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:26.63242+00:00
-- url     : https://prove2.me/submissions/167e0ea4-3aa9-4682-9da4-c16feacccca8

-- Solution generated from lean/HomogeneousCharts.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_criticalZero_homogeneousChart
import Theorems.Thm_CurveSymmetry_criticalZero_transport
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
lemma familyBihomogeneous_mixed (m : ℕ) (α u y : ℂ) :
    familyBihomogeneous m α ![1, u] ![y, 1] =
      planeEval u y (familyMixedPolynomial m α (star α)) := by
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul, familyMixedPolynomial,
    map_add, map_mul, map_pow, planeEval_C, planeEval_X_zero, planeEval_X_one]
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

section
open CurveSymmetry
set_option autoImplicit false
open Filter
open scoped Topology
theorem solution (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![1, x], ![y, 1]) ↔ JacobianSingular (familyMixedPolynomial m α (star α)) x y := by
  let e := ContinuousLinearEquiv.refl ℂ (Fin 2 → ℂ)
  have he (v : Fin 2 → ℂ) :
      familyBihomogeneous m α (reverseCoordinates ![v 0, 1])
        (e ![v 1, 1]) = MvPolynomial.eval v (familyMixedPolynomial m α (star α)) := by
    simp only [e, ContinuousLinearEquiv.refl_apply, reverseCoordinates_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      familyBihomogeneous_mixed, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  simpa only [e, ContinuousLinearEquiv.refl_apply, reverseCoordinates_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
    family_critical_chart_iff m α _ reverseCoordinates e he x y
end

#print axioms solution
