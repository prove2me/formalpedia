-- Prove2me | solution 1 for DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7f7d6462-9b08-580b-9eb9-a535252b8bfa

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support
import Theorems.Thm_DixmierMalliavin_exists_eq_integral_mul_comp_mul_exp_smul_add
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul

set_option autoImplicit false

set_option autoImplicit false

open scoped Topology
open Filter

noncomputable section

namespace AlgebraFactorization

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

private def flowProd {k : ℕ} (X : Fin k → A) (t : Fin k → ℝ) : A :=
  (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod

private theorem flowProd_zero (X : Fin 0 → A) (t : Fin 0 → ℝ) : flowProd X t = 1 := by
  simp [flowProd]

private theorem flowProd_succ {k : ℕ} (X : Fin (k + 1) → A) (t : Fin (k + 1) → ℝ) :
    flowProd X t = flowProd (fun i => X (Fin.castSucc i)) (fun i => t (Fin.castSucc i)) *
      NormedSpace.exp (t (Fin.last k) • X (Fin.last k)) := by
  simp only [flowProd]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

private theorem flowProd_at_zero : ∀ {k : ℕ} (X : Fin k → A), flowProd X (fun _ => 0) = 1
  | 0, X => flowProd_zero X _
  | k + 1, X => by
    rw [flowProd_succ, zero_smul, NormedSpace.exp_zero, mul_one]
    exact flowProd_at_zero _

section Complete

variable [CompleteSpace A]

private theorem contDiff_nat_exp_smul (X : A) : ∀ n : ℕ, ContDiff ℝ n (fun s : ℝ => NormedSpace.exp (s • X))
  | 0 => by
    have hd : Differentiable ℝ (fun s : ℝ => NormedSpace.exp (s • X)) :=
      fun s => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).differentiableAt
    simpa only [Nat.cast_zero, contDiff_zero] using hd.continuous
  | n + 1 => by
    have hd : Differentiable ℝ (fun s : ℝ => NormedSpace.exp (s • X)) :=
      fun s => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).differentiableAt
    have hder : deriv (fun s : ℝ => NormedSpace.exp (s • X)) =
        fun s : ℝ => NormedSpace.exp (s • X) * X :=
      funext fun s => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨hd, fun h => absurd h (by simp), ?_⟩
    rw [hder]
    exact (contDiff_nat_exp_smul X n).mul contDiff_const

private theorem contDiff_exp_smul (X : A) : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => NormedSpace.exp (s • X)) :=
  contDiff_infty.mpr fun n => contDiff_nat_exp_smul X n

private theorem contDiff_flowProd : ∀ {k : ℕ} (X : Fin k → A), ContDiff ℝ (⊤ : ℕ∞) (flowProd X)
  | 0, X => by
    have : flowProd X = fun _ => 1 := funext fun t => flowProd_zero X t
    rw [this]
    exact contDiff_const
  | k + 1, X => by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : Fin (k + 1) → ℝ =>
        flowProd (fun i => X (Fin.castSucc i)) (fun i => t (Fin.castSucc i))) :=
      (contDiff_flowProd _).comp (contDiff_pi.mpr fun i => contDiff_apply ℝ ℝ (Fin.castSucc i))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t : Fin (k + 1) → ℝ =>
        NormedSpace.exp (t (Fin.last k) • X (Fin.last k))) :=
      (contDiff_exp_smul (X (Fin.last k))).comp (contDiff_apply ℝ ℝ (Fin.last k))
    have : flowProd X = fun t => flowProd (fun i => X (Fin.castSucc i)) (fun i => t (Fin.castSucc i)) *
        NormedSpace.exp (t (Fin.last k) • X (Fin.last k)) :=
      funext fun t => flowProd_succ X t
    rw [this]
    exact h1.mul h2

private theorem hasDerivAt_flowProd_line :
    ∀ {k : ℕ} (Y : Fin k → A), HasDerivAt (fun s : ℝ => flowProd Y (fun _ => s)) (∑ i, Y i) 0
  | 0, Y => by
    simp only [flowProd_zero, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const 0 1
  | k + 1, Y => by
    have ih := hasDerivAt_flowProd_line (fun i => Y (Fin.castSucc i))
    have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Y (Fin.last k)))
        (NormedSpace.exp ((0 : ℝ) • Y (Fin.last k)) * Y (Fin.last k)) 0 :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y (Fin.last k)) 0
    have h := ih.mul h2
    have hfun : (fun s : ℝ => flowProd Y (fun _ => s)) =
        (fun s : ℝ => flowProd (fun i => Y (Fin.castSucc i)) (fun _ => s)) *
          fun s : ℝ => NormedSpace.exp (s • Y (Fin.last k)) := by
      funext s
      exact flowProd_succ Y (fun _ => s)
    rw [hfun]
    convert h using 1
    rw [flowProd_at_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, one_mul,
      Fin.sum_univ_castSucc]

end Complete

section Chart

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ A)

private def chart (T : A) : A := flowProd (fun i => b i) (b.equivFunL T)

private theorem chart_zero : chart b 0 = 1 := by
  simp only [chart, map_zero]
  exact flowProd_at_zero _

private theorem chart_smul (s : ℝ) (v : A) :
    chart b (s • v) = flowProd (fun i => b.equivFunL v i • b i) (fun _ => s) := by
  simp only [chart, map_smul, flowProd]
  congr 1
  refine List.ofFn_inj.mpr ?_
  funext i
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

end Chart

section ChartCalculus

variable [CompleteSpace A] {d : ℕ} (b : Module.Basis (Fin d) ℝ A)

private theorem contDiff_chart : ContDiff ℝ (⊤ : ℕ∞) (chart b) :=
  (contDiff_flowProd _).comp b.equivFunL.contDiff

private theorem hasDerivAt_chart_line (v : A) : HasDerivAt (fun s : ℝ => chart b (s • v)) v 0 := by
  have h := hasDerivAt_flowProd_line (A := A) (fun i => b.equivFunL v i • b i)
  have hsum : (∑ i, b.equivFunL v i • b i) = v := b.sum_equivFun v
  rw [hsum] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact chart_smul b s v

private theorem fderiv_chart_zero : fderiv ℝ (chart b) 0 = ContinuousLinearMap.id ℝ A := by
  have hdiff : DifferentiableAt ℝ (chart b) 0 :=
    ((contDiff_chart b).differentiable (by simp)).differentiableAt
  ext v
  have h1 : HasDerivAt (fun s : ℝ => chart b (s • v)) (fderiv ℝ (chart b) 0 v) 0 := by
    have hl : HasDerivAt (fun s : ℝ => s • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h1.unique (hasDerivAt_chart_line b v)

private theorem hasFDerivAt_chart_zero :
    HasFDerivAt (chart b) ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
  rw [ContinuousLinearEquiv.coe_refl, ← fderiv_chart_zero b]
  exact ((contDiff_chart b).differentiable (by simp)).differentiableAt.hasFDerivAt

private def chartHomeo₀ : OpenPartialHomeomorph A A :=
  (contDiff_chart b).contDiffAt.toOpenPartialHomeomorph (chart b) (hasFDerivAt_chart_zero b)
    (by simp)

private theorem chartHomeo₀_coe : (chartHomeo₀ b : A → A) = chart b := rfl

private theorem zero_mem_chartHomeo₀_source : (0 : A) ∈ (chartHomeo₀ b).source :=
  (contDiff_chart b).contDiffAt.mem_toOpenPartialHomeomorph_source (hasFDerivAt_chart_zero b)
    (by simp)

private def goodSet : Set A := {T | 0 < (fderiv ℝ (chart b) T).det}

private theorem isOpen_goodSet : IsOpen (goodSet b) := by
  have hc : Continuous (fderiv ℝ (chart b)) := (contDiff_chart b).continuous_fderiv (by simp)
  exact isOpen_lt continuous_const (ContinuousLinearMap.continuous_det.comp hc)

private theorem zero_mem_goodSet : (0 : A) ∈ goodSet b := by
  simp only [goodSet, Set.mem_setOf_eq, fderiv_chart_zero]
  have : (ContinuousLinearMap.id ℝ A).det = 1 := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [this]
  exact one_pos

private def chartHomeo : OpenPartialHomeomorph A A :=
  (chartHomeo₀ b).restrOpen (goodSet b) (isOpen_goodSet b)

private theorem chartHomeo_coe : (chartHomeo b : A → A) = chart b := rfl

private theorem chartHomeo_source : (chartHomeo b).source = (chartHomeo₀ b).source ∩ goodSet b := by
  simp [chartHomeo]

private theorem zero_mem_chartHomeo_source : (0 : A) ∈ (chartHomeo b).source := by
  rw [chartHomeo_source]
  exact ⟨zero_mem_chartHomeo₀_source b, zero_mem_goodSet b⟩

private theorem isOpen_chartHomeo_source : IsOpen (chartHomeo b).source := (chartHomeo b).open_source

private theorem det_fderiv_chart_pos {T : A} (hT : T ∈ (chartHomeo b).source) :
    0 < (fderiv ℝ (chart b) T).det := by
  rw [chartHomeo_source] at hT
  exact hT.2

variable [FiniteDimensional ℝ A]

private def derivEquiv {T : A} (hT : T ∈ (chartHomeo b).source) : A ≃L[ℝ] A :=
  (fderiv ℝ (chart b) T).toContinuousLinearEquivOfDetNeZero (det_fderiv_chart_pos b hT).ne'

private theorem coe_derivEquiv {T : A} (hT : T ∈ (chartHomeo b).source) :
    (derivEquiv b hT : A →L[ℝ] A) = fderiv ℝ (chart b) T :=
  ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _

private theorem hasFDerivAt_chart_of_mem {T : A} (hT : T ∈ (chartHomeo b).source) :
    HasFDerivAt (chartHomeo b) ((derivEquiv b hT : A ≃L[ℝ] A) : A →L[ℝ] A) T := by
  rw [coe_derivEquiv, chartHomeo_coe]
  exact ((contDiff_chart b).differentiable (by simp)).differentiableAt.hasFDerivAt

private theorem contDiffAt_chartHomeo_symm {y : A} (hy : y ∈ (chartHomeo b).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (chartHomeo b).symm y := by
  have hx : (chartHomeo b).symm y ∈ (chartHomeo b).source := (chartHomeo b).map_target hy
  exact (chartHomeo b).contDiffAt_symm hy (hasFDerivAt_chart_of_mem b hx)
    ((contDiff_chart b).contDiffAt)

private theorem contDiffOn_chartHomeo_symm : ContDiffOn ℝ (⊤ : ℕ∞) (chartHomeo b).symm (chartHomeo b).target :=
  fun _ hy => (contDiffAt_chartHomeo_symm b hy).contDiffWithinAt

private theorem det_fderiv_chartHomeo_symm_pos {y : A} (hy : y ∈ (chartHomeo b).target) :
    0 < (fderiv ℝ (chartHomeo b).symm y).det := by
  have hx : (chartHomeo b).symm y ∈ (chartHomeo b).source := (chartHomeo b).map_target hy
  have h := (chartHomeo b).hasFDerivAt_symm hy (hasFDerivAt_chart_of_mem b hx)
  rw [h.fderiv, ContinuousLinearEquiv.det_coe_symm, coe_derivEquiv]
  exact inv_pos.mpr (det_fderiv_chart_pos b hx)

end ChartCalculus

end AlgebraFactorization

end

set_option autoImplicit false

open scoped Topology
open Filter MeasureTheory Set

noncomputable section

namespace AlgebraFactorization

section Det

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

private theorem det_eq_sum_perm {d : ℕ} (b : Module.Basis (Fin d) ℝ A) (L : A →L[ℝ] A) :
    L.det = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, b.repr (L (b i)) (σ i) := by
  rw [show L.det = LinearMap.det (L : A →ₗ[ℝ] A) from rfl, ← LinearMap.det_toMatrix b,
    Matrix.det_apply']
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]

private theorem contDiff_det {d : ℕ} (b : Module.Basis (Fin d) ℝ A) :
    ContDiff ℝ (⊤ : ℕ∞) (fun L : A →L[ℝ] A => L.det) := by
  haveI : FiniteDimensional ℝ A := b.finiteDimensional_of_finite
  have hcoord : ∀ i j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun L : A →L[ℝ] A => b.repr (L (b i)) j) := by
    intro i j
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun L : A →L[ℝ] A => L (b i)) :=
      contDiff_id.clm_apply contDiff_const
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : A => b.equivFunL v j) :=
      (contDiff_apply ℝ ℝ j).comp b.equivFunL.contDiff
    exact h2.comp h1
  have heq : (fun L : A →L[ℝ] A => L.det) = fun L =>
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, b.repr (L (b i)) (σ i) :=
    funext fun L => det_eq_sum_perm b L
  rw [heq]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hcoord i (σ i))

end Det

section ZeroExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

private theorem contDiff_of_contDiffOn_of_eq_zero {f : E → F} {O S : Set E} (hO : IsOpen O)
    (hS : IsClosed S) (hSO : S ⊆ O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (h0 : ∀ x ∉ S, f x = 0) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hf.contDiffAt (hO.mem_nhds hx)
  · have hxS : x ∉ S := fun h => hx (hSO h)
    have hev : f =ᶠ[𝓝 x] fun _ => (0 : F) :=
      Filter.eventuallyEq_of_mem (hS.isOpen_compl.mem_nhds hxS) fun y hy => h0 y hy
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev

end ZeroExtension

section Pushforward

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
  [FiniteDimensional ℝ A] (μ : Measure A) [μ.IsAddHaarMeasure]

private theorem exists_pushforward {d : ℕ} (b : Module.Basis (Fin d) ℝ A) (P : OpenPartialHomeomorph A A)
    (hsymm : ContDiffOn ℝ (⊤ : ℕ∞) P.symm P.target)
    (hpos : ∀ y ∈ P.target, 0 < (fderiv ℝ P.symm y).det)
    (F : A → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFs : tsupport F ⊆ P.source) :
    ∃ Ψ : A → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ P '' tsupport F ∧
      ∀ G : A → ℂ, ∫ T, F T * G (P T) ∂μ = ∫ y, Ψ y * G y ∂μ := by
  set J : A → ℝ := fun y => |(fderiv ℝ P.symm y).det| with hJ
  set Ψ : A → ℂ := P.target.indicator fun y => ((J y : ℝ) : ℂ) * F (P.symm y) with hΨ
  have hK : IsCompact (P '' tsupport F) := hFc.image_of_continuousOn (P.continuousOn.mono hFs)
  have hKt : P '' tsupport F ⊆ P.target := by
    rintro y ⟨T, hT, rfl⟩
    exact P.map_source (hFs hT)
  have hΨ0 : ∀ y ∉ P '' tsupport F, Ψ y = 0 := by
    intro y hy
    by_cases hyt : y ∈ P.target
    · have hF0 : F (P.symm y) = 0 := by
        by_contra hne
        exact hy ⟨P.symm y, subset_tsupport _ hne, P.right_inv hyt⟩
      simp only [hΨ, Set.indicator_of_mem hyt, hF0, mul_zero]
    · simp only [hΨ, Set.indicator_of_notMem hyt]
  have htsupp : tsupport Ψ ⊆ P '' tsupport F :=
    closure_minimal (fun y hy => Classical.byContradiction fun h => hy (hΨ0 y h)) hK.isClosed
  have hcs : HasCompactSupport Ψ := hK.of_isClosed_subset (isClosed_tsupport Ψ) htsupp

  have hdiff : DifferentiableOn ℝ P.symm P.target := hsymm.differentiableOn (by simp)
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (fderiv ℝ P.symm y).det) P.target :=
    (contDiff_det b).comp_contDiffOn (hsymm.fderiv_of_isOpen (m := (⊤ : ℕ∞)) P.open_target (by simp))
  have hJs : ContDiffOn ℝ (⊤ : ℕ∞) J P.target :=
    hdet.congr fun y hy => by simp only [hJ, abs_of_pos (hpos y hy)]
  have hJc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((J y : ℝ) : ℂ)) P.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hJs
  have hFsymm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F (P.symm y)) P.target := hF.comp_contDiffOn hsymm
  have hΨon : ContDiffOn ℝ (⊤ : ℕ∞) Ψ P.target :=
    (hJc.mul hFsymm).congr fun y hy => by simp only [hΨ, Set.indicator_of_mem hy]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Ψ :=
    contDiff_of_contDiffOn_of_eq_zero P.open_target hK.isClosed hKt hΨon hΨ0
  refine ⟨Ψ, hsmooth, hcs, htsupp, fun G => ?_⟩

  have h1 : ∫ T, F T * G (P T) ∂μ = ∫ T in P.source, F T * G (P T) ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun T hT => ?_).symm
    have : F T = 0 := image_eq_zero_of_notMem_tsupport fun h => hT (hFs h)
    simp only [this, zero_mul]
  have h2 : ∫ y, Ψ y * G y ∂μ = ∫ y in P.target, ((J y : ℝ) : ℂ) * F (P.symm y) * G y ∂μ := by
    rw [← integral_indicator P.open_target.measurableSet]
    congr 1
    funext y
    by_cases hy : y ∈ P.target
    · simp only [hΨ, Set.indicator_of_mem hy]
    · simp only [hΨ, Set.indicator_of_notMem hy, zero_mul]
  have hd : ∀ y ∈ P.target, HasFDerivWithinAt P.symm (fderiv ℝ P.symm y) P.target y := fun y hy =>
    ((hdiff y hy).differentiableAt (P.open_target.mem_nhds hy)).hasFDerivAt.hasFDerivWithinAt
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul μ P.open_target.measurableSet hd
    P.symm.injOn (fun T => F T * G (P T))
  rw [h1, h2, ← P.symm_image_target_eq_source, hcov]
  refine setIntegral_congr_fun P.open_target.measurableSet fun y hy => ?_
  simp only [hJ, P.right_inv hy, Complex.real_smul, mul_assoc]

end Pushforward

end AlgebraFactorization

end

namespace AlgebraFactorization

open scoped Topology
open Filter MeasureTheory Set

section CubeForm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private def cube (k : ℕ) (ε : ℝ) : Set (Fin k → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-ε) ε

private theorem isCompact_cube (k : ℕ) (ε : ℝ) : IsCompact (cube k ε) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem isClosed_cube (k : ℕ) (ε : ℝ) : IsClosed (cube k ε) := (isCompact_cube k ε).isClosed

private theorem mem_cube_iff {k : ℕ} {ε : ℝ} {t : Fin k → ℝ} : t ∈ cube k ε ↔ ∀ i, t i ∈ Set.Icc (-ε) ε :=
  Set.mem_univ_pi

variable (A) in
private def OneParameterStep : Prop :=
  ∀ (X : A) (ε : ℝ), 0 < ε → ∀ (Φ : A → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
    ∃ (Φ₁ : A → ℂ) (φ ψ : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ tsupport Φ₁ ⊆ tsupport Φ ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      tsupport φ ⊆ Set.Icc (-ε) ε ∧ tsupport ψ ⊆ Set.Icc (-ε) ε ∧
      ∀ x : A, Φ x = (∫ t, φ t * Φ₁ (x * NormedSpace.exp (t • X))) +
        ∫ t, ψ t * Φ (x * NormedSpace.exp (t • X))

private def CubeForm (k : ℕ) (X : Fin k → A) (ε : ℝ) (Φ : A → ℂ) : Prop :=
  ∃ (Φw : (Fin k → Bool) → A → ℂ) (Fw : (Fin k → Bool) → (Fin k → ℝ) → ℂ),
    (∀ w, ContDiff ℝ (⊤ : ℕ∞) (Φw w) ∧ tsupport (Φw w) ⊆ tsupport Φ) ∧
    (∀ w, ContDiff ℝ (⊤ : ℕ∞) (Fw w) ∧ tsupport (Fw w) ⊆ cube k ε) ∧
    ∀ x : A, Φ x = ∑ w, ∫ t, Fw w t * Φw w (x * flowProd X t)

private theorem integral_finZero (g : (Fin 0 → ℝ) → ℂ) : ∫ t, g t = g default := by
  rw [MeasureTheory.volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ)) default,
    integral_dirac]

omit [CompleteSpace A] in
private theorem cubeForm_zero (X : Fin 0 → A) (ε : ℝ) (Φ : A → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    CubeForm 0 X ε Φ := by
  refine ⟨fun _ => Φ, fun _ _ => 1, fun _ => ⟨hΦ, subset_rfl⟩, fun _ => ⟨contDiff_const, ?_⟩, ?_⟩
  · intro t _
    exact mem_cube_iff.mpr fun i => Fin.elim0 i
  · intro x
    simp only [Finset.univ_unique, Finset.sum_singleton, integral_finZero, one_mul]
    rw [flowProd]
    simp

private theorem piFinSuccAbove_last_apply (k : ℕ) (u : Fin (k + 1) → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k) u = (u (Fin.last k), Fin.init u) := by
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  · funext j
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]

private theorem hasCompactSupport_prodFun {k : ℕ} {φ : ℝ → ℂ} {F : (Fin k → ℝ) → ℂ}
    (hφ : HasCompactSupport φ) (hF : HasCompactSupport F) :
    HasCompactSupport fun p : ℝ × (Fin k → ℝ) => φ p.1 * F p.2 := by
  refine IsCompact.of_isClosed_subset (hφ.prod hF) (isClosed_tsupport _) ?_
  refine closure_minimal ?_ ((isClosed_tsupport φ).prod (isClosed_tsupport F))
  intro p hp
  rw [Function.mem_support, mul_ne_zero_iff] at hp
  exact ⟨subset_tsupport _ hp.1, subset_tsupport _ hp.2⟩

omit [CompleteSpace A] in
private theorem flowProd_succ_init {k : ℕ} (X : Fin (k + 1) → A) (t : Fin (k + 1) → ℝ) :
    flowProd X t = flowProd (fun i => X (Fin.castSucc i)) (Fin.init t) *
      NormedSpace.exp (t (Fin.last k) • X (Fin.last k)) :=
  flowProd_succ X t

private theorem cubeForm_succ (hstep : OneParameterStep A) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (X : Fin (k + 1) → A) (Φ : A → ℂ)
    (hΦc : HasCompactSupport Φ)
    (ih : CubeForm k (fun i => X (Fin.castSucc i)) ε Φ) : CubeForm (k + 1) X ε Φ := by
  obtain ⟨Φw, Fw, hΦw, hFw, hrep⟩ := ih
  set Xk : Fin k → A := fun i => X (Fin.castSucc i) with hXk
  set Y : A := X (Fin.last k) with hY
  have hΦwc : ∀ w, HasCompactSupport (Φw w) := fun w =>
    IsCompact.of_isClosed_subset hΦc (isClosed_tsupport _) (hΦw w).2

  choose Φ1 φ ψ hΦ1s hΦ1t hφs hψs hφt hψt hstep using fun w => hstep Y ε hε (Φw w) (hΦw w).1 (hΦwc w)
  have hΦ1 : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Φ1 w) ∧ tsupport (Φ1 w) ⊆ tsupport (Φw w) := fun w => ⟨hΦ1s w, hΦ1t w⟩
  have hφ : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (φ w) ∧ tsupport (φ w) ⊆ Set.Icc (-ε) ε := fun w => ⟨hφs w, hφt w⟩
  have hψ : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (ψ w) ∧ tsupport (ψ w) ⊆ Set.Icc (-ε) ε := fun w => ⟨hψs w, hψt w⟩

  let Φw' : (Fin (k + 1) → Bool) → A → ℂ := fun w' =>
    if w' (Fin.last k) then Φ1 (Fin.init w') else Φw (Fin.init w')
  let χ : (Fin (k + 1) → Bool) → ℝ → ℂ := fun w' =>
    if w' (Fin.last k) then φ (Fin.init w') else ψ (Fin.init w')
  let Fw' : (Fin (k + 1) → Bool) → (Fin (k + 1) → ℝ) → ℂ := fun w' u =>
    χ w' (u (Fin.last k)) * Fw (Fin.init w') (Fin.init u)
  have hχ : ∀ w', ContDiff ℝ (⊤ : ℕ∞) (χ w') ∧ tsupport (χ w') ⊆ Set.Icc (-ε) ε := by
    intro w'
    by_cases h : w' (Fin.last k) <;> simp only [χ, h, if_true, if_false, Bool.false_eq_true]
    · exact hφ _
    · exact hψ _
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (Fin.init : (Fin (k + 1) → ℝ) → (Fin k → ℝ)) :=
    contDiff_pi.mpr fun i => contDiff_apply ℝ ℝ (Fin.castSucc i)
  refine ⟨Φw', Fw', ?_, ?_, ?_⟩
  · intro w'
    by_cases h : w' (Fin.last k) <;> simp only [Φw', h, if_true, if_false, Bool.false_eq_true]
    · exact ⟨(hΦ1 _).1, (hΦ1 _).2.trans (hΦw _).2⟩
    · exact hΦw _
  · intro w'
    refine ⟨((hχ w').1.comp (contDiff_apply ℝ ℝ (Fin.last k))).mul ((hFw _).1.comp hinit), ?_⟩
    refine closure_minimal ?_ (isClosed_cube _ _)
    intro u hu
    rw [Function.mem_support, mul_ne_zero_iff] at hu
    have h1 : u (Fin.last k) ∈ Set.Icc (-ε) ε := (hχ w').2 (subset_tsupport _ hu.1)
    have h2 : Fin.init u ∈ cube k ε := (hFw _).2 (subset_tsupport _ hu.2)
    rw [mem_cube_iff] at h2 ⊢
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h1
    · exact h2 j
  · intro x

    have key : ∀ w, ∫ t, Fw w t * Φw w (x * flowProd Xk t) =
        (∫ u, Fw' (Fin.snoc w true) u * Φw' (Fin.snoc w true) (x * flowProd X u)) +
          ∫ u, Fw' (Fin.snoc w false) u * Φw' (Fin.snoc w false) (x * flowProd X u) := by
      intro w

      let g1 : ℝ × (Fin k → ℝ) → ℂ := fun p =>
        (φ w p.1 * Fw w p.2) * Φ1 w (x * flowProd Xk p.2 * NormedSpace.exp (p.1 • Y))
      let g0 : ℝ × (Fin k → ℝ) → ℂ := fun p =>
        (ψ w p.1 * Fw w p.2) * Φw w (x * flowProd Xk p.2 * NormedSpace.exp (p.1 • Y))
      have hcont_flow : Continuous fun p : ℝ × (Fin k → ℝ) =>
          x * flowProd Xk p.2 * NormedSpace.exp (p.1 • Y) :=
        ((continuous_const.mul ((contDiff_flowProd Xk).continuous.comp continuous_snd)).mul
          ((contDiff_exp_smul Y).continuous.comp continuous_fst))
      have hg1c : Continuous g1 :=
        (((hφ w).1.continuous.comp continuous_fst).mul ((hFw w).1.continuous.comp continuous_snd)).mul
          ((hΦ1 w).1.continuous.comp hcont_flow)
      have hg0c : Continuous g0 :=
        (((hψ w).1.continuous.comp continuous_fst).mul ((hFw w).1.continuous.comp continuous_snd)).mul
          ((hΦw w).1.continuous.comp hcont_flow)
      have hφc : HasCompactSupport (φ w) :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hφ w).2
      have hψc : HasCompactSupport (ψ w) :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hψ w).2
      have hFwc : HasCompactSupport (Fw w) :=
        IsCompact.of_isClosed_subset (isCompact_cube k ε) (isClosed_tsupport _) (hFw w).2
      have hg1i : Integrable g1 ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))) := by
        rw [← Measure.volume_eq_prod]
        exact hg1c.integrable_of_hasCompactSupport ((hasCompactSupport_prodFun hφc hFwc).mul_right)
      have hg0i : Integrable g0 ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))) := by
        rw [← Measure.volume_eq_prod]
        exact hg0c.integrable_of_hasCompactSupport ((hasCompactSupport_prodFun hψc hFwc).mul_right)

      have hpt : ∀ t, Fw w t * Φw w (x * flowProd Xk t) = (∫ s, g1 (s, t)) + ∫ s, g0 (s, t) := by
        intro t
        rw [hstep w (x * flowProd Xk t), mul_add, ← integral_const_mul, ← integral_const_mul]
        congr 1 <;> refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_) <;>
          (simp only [g1, g0]; ring)

      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
      have hI : ∀ (g : ℝ × (Fin k → ℝ) → ℂ),
          Integrable g ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))) →
            ∫ t, ∫ s, g (s, t) = ∫ u : Fin (k + 1) → ℝ, g (u (Fin.last k), Fin.init u) := by
        intro g hg
        rw [← integral_prod_symm g hg, ← Measure.volume_eq_prod, ← hmp.integral_comp']
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [piFinSuccAbove_last_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hg1i.integral_prod_right
        hg0i.integral_prod_right, hI g1 hg1i, hI g0 hg0i]
      congr 1 <;> refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_) <;>
        simp only [g1, g0, Fw', Φw', χ, Fin.snoc_last, Fin.init_snoc,
          Bool.false_eq_true, if_true, if_false, flowProd_succ_init, mul_assoc, hXk, hY]
    calc Φ x = ∑ w, ∫ t, Fw w t * Φw w (x * flowProd Xk t) := hrep x
      _ = ∑ w, ((∫ u, Fw' (Fin.snoc w true) u * Φw' (Fin.snoc w true) (x * flowProd X u)) +
            ∫ u, Fw' (Fin.snoc w false) u * Φw' (Fin.snoc w false) (x * flowProd X u)) :=
          Finset.sum_congr rfl fun w _ => key w
      _ = ∑ w', ∫ u, Fw' w' u * Φw' w' (x * flowProd X u) := by
          rw [← Equiv.sum_comp (Fin.snocEquiv fun _ => Bool), Fintype.sum_prod_type, Fintype.sum_bool,
            Finset.sum_add_distrib]
          rfl

private theorem cubeForm (hstep : OneParameterStep A) {ε : ℝ} (hε : 0 < ε) :
    ∀ (k : ℕ) (X : Fin k → A) (Φ : A → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      CubeForm k X ε Φ := by
  intro k
  induction k with
  | zero => intro X Φ hΦ _; exact cubeForm_zero X ε Φ hΦ
  | succ k ih =>
    intro X Φ hΦ hΦc
    exact cubeForm_succ hstep hε X Φ hΦc (ih (fun i => X (Fin.castSucc i)) Φ hΦ hΦc)

end CubeForm

section Assembly

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

private theorem exists_volume_transfer {d : ℕ} (b : Module.Basis (Fin d) ℝ A) :
    ∃ c : NNReal, ∀ g : (Fin d → ℝ) → ℂ, ∫ t, g t = c • ∫ T, g (b.equivFunL T) ∂μ := by
  let e : A ≃L[ℝ] (Fin d → ℝ) := b.equivFunL
  let eM : (Fin d → ℝ) ≃ᵐ A := e.symm.toHomeomorph.toMeasurableEquiv
  let ν : Measure A := Measure.map eM volume
  haveI hν : ν.IsAddHaarMeasure := by
    change (Measure.map (e.symm.toHomeomorph.toMeasurableEquiv : (Fin d → ℝ) → A) volume).IsAddHaarMeasure
    rw [Homeomorph.toMeasurableEquiv_coe]
    exact e.symm.isAddHaarMeasure_map volume
  refine ⟨Measure.addHaarScalarFactor ν μ, fun g => ?_⟩
  have h1 : ∫ t, g t = ∫ T, g (e T) ∂ν := by
    change ∫ t, g t = ∫ T, g (e T) ∂(Measure.map eM volume)
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change g t = g (e (e.symm.toHomeomorph.toMeasurableEquiv t))
    rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.apply_symm_apply]
  have h2 : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have h3 : ∫ T, g (e T) ∂ν = ∫ T, g (e T) ∂(Measure.addHaarScalarFactor ν μ • μ) := by rw [← h2]
  rw [h1, h3, integral_smul_nnreal_measure]

omit [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] in
private theorem exists_cube_subset {d : ℕ} (b : Module.Basis (Fin d) ℝ A) {O : Set A} (hO : O ∈ 𝓝 (0 : A)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ cube d ε, b.equivFunL.symm t ∈ O := by
  have h0 : b.equivFunL.symm ⁻¹' O ∈ 𝓝 (0 : Fin d → ℝ) :=
    b.equivFunL.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hO)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp h0
  refine ⟨r / 2, by positivity, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
  intro i
  have hi := (mem_cube_iff.mp ht) i
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hi.1, hi.2]

variable [CompleteSpace A]

private theorem dm_alg {d : ℕ} (b : Module.Basis (Fin d) ℝ A) (hstep : OneParameterStep A) (U : Set A)
    (hU : U ∈ 𝓝 (1 : A)) (Φ : A → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (Φ' Ψ : Fin n → A → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U) ∧
      ∀ x : A, Φ x = ∑ k, ∫ y, Φ' k (x * y) * Ψ k y ∂μ := by
  classical

  have hO : (chartHomeo b).source ∩ chart b ⁻¹' U ∈ 𝓝 (0 : A) := by
    refine Filter.inter_mem ((chartHomeo b).open_source.mem_nhds (zero_mem_chartHomeo_source b)) ?_
    exact (contDiff_chart b).continuous.continuousAt.preimage_mem_nhds (by rwa [chart_zero])
  obtain ⟨ε, hε, hcube⟩ := exists_cube_subset b hO

  obtain ⟨Φw, Fw, hΦw, hFw, hrep⟩ := cubeForm hstep hε d (fun i => b i) Φ hΦ hΦc

  obtain ⟨c, hc⟩ := exists_volume_transfer μ b

  let Ft : (Fin d → Bool) → A → ℂ := fun w T => ((c : ℝ) : ℂ) * Fw w (b.equivFunL T)
  have hFt : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ft w) := fun w =>
    contDiff_const.mul ((hFw w).1.comp b.equivFunL.contDiff)
  have hFt_supp : ∀ w, tsupport (Ft w) ⊆ b.equivFunL ⁻¹' cube d ε := by
    intro w
    refine closure_minimal (fun T hT => ?_) ((isClosed_cube d ε).preimage b.equivFunL.continuous)
    rw [Function.mem_support] at hT
    have h' : Fw w (b.equivFunL T) ≠ 0 := fun h0 => hT (by simp only [Ft, h0, mul_zero])
    exact (hFw w).2 (subset_tsupport _ h')
  have hFt_src : ∀ w, tsupport (Ft w) ⊆ (chartHomeo b).source := by
    intro w T hT
    have h := hcube (b.equivFunL T) (hFt_supp w hT)
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h.1
  have hFt_cs : ∀ w, HasCompactSupport (Ft w) := fun w =>
    IsCompact.of_isClosed_subset (b.equivFunL.toHomeomorph.isCompact_preimage.mpr (isCompact_cube d ε))
      (isClosed_tsupport _) (hFt_supp w)

  choose Ψw hΨs hΨc hΨsupp hΨint using fun w =>
    exists_pushforward μ b (chartHomeo b) (contDiffOn_chartHomeo_symm b)
      (fun y hy => det_fderiv_chartHomeo_symm_pos b hy) (Ft w) (hFt w) (hFt_cs w) (hFt_src w)

  have hΨU : ∀ w, tsupport (Ψw w) ⊆ U := by
    intro w y hy
    obtain ⟨T, hT, rfl⟩ := hΨsupp w hy
    have h := hcube (b.equivFunL T) (hFt_supp w hT)
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h.2

  have hleaf : ∀ w x, ∫ t, Fw w t * Φw w (x * flowProd (fun i => b i) t) =
      ∫ y, Ψw w y * Φw w (x * y) ∂μ := by
    intro w x
    rw [hc, NNReal.smul_def, Complex.real_smul, ← integral_const_mul]
    rw [← hΨint w (fun y => Φw w (x * y))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun T => ?_)
    simp only [Ft, mul_assoc]
    rfl
  have hsum : ∀ x, Φ x = ∑ w, ∫ y, Φw w (x * y) * Ψw w y ∂μ := by
    intro x
    rw [hrep x]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hleaf w x]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

  let ι : (Fin d → Bool) ≃ Fin (Fintype.card (Fin d → Bool)) := Fintype.equivFin _
  refine ⟨Fintype.card (Fin d → Bool), fun k => Φw (ι.symm k), fun k => Ψw (ι.symm k),
    fun k => hΦw _, fun k => ⟨hΨs _, hΨc _, hΨU _⟩, fun x => ?_⟩
  rw [hsum x]
  exact (Equiv.sum_comp ι.symm (fun w => ∫ y, Φw w (x * y) * Ψw w y ∂μ)).symm

end Assembly

section Key

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

omit [MeasurableSpace A] [BorelSpace A] in
private theorem completeSpace_of_finiteDimensional : CompleteSpace A := FiniteDimensional.complete ℝ A

private theorem exists_factorization_of_oneParameter (hstep : OneParameterStep A) (U : Set A)
    (hU : U ∈ nhds (1 : A)) (Φ : A → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (Φ' Ψ : Fin n → A → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U) ∧
      ∀ x : A, Φ x = ∑ k, ∫ y, Φ' k (x * y) * Ψ k y ∂μ :=
  haveI : CompleteSpace A := completeSpace_of_finiteDimensional
  dm_alg μ (Module.finBasis ℝ A) hstep U hU Φ hΦ hΦc

end Key

end AlgebraFactorization

theorem solution {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
    (μ : MeasureTheory.Measure A) [μ.IsAddHaarMeasure] (U : Set A) (hU : U ∈ nhds (1 : A))
    (Φ : A → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (Φ' Ψ : Fin n → A → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U) ∧
      ∀ x : A, Φ x = ∑ k, ∫ y, Φ' k (x * y) * Ψ k y ∂μ := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  exact AlgebraFactorization.exists_factorization_of_oneParameter μ
    (fun X ε hε Φ hΦ hΦc => DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add X ε hε Φ hΦ hΦc)
    U hU Φ hΦ hΦc

end S_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul
end P2MW
export P2MW.S_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul (solution)
