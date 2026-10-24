-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:44:46.319543+00:00
-- url     : https://prove2.me/submissions/de61891b-7c4d-49f6-966b-efd27dfdbdfe

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gammaTwo_eq_hessianSqStdBasis_add_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_approx_of_lipschitz_gradient_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)
end Gradient
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
omit [CompleteSpace E] in
/-- The Laplacian as the trace of the iterated directional derivatives, at a point where the
derivative is differentiable. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply {g : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    Laplacian.laplacian g x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hg _ _).symm
omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
omit [CompleteSpace E] in
/-- The Laplacian of a `C^n` function is `C^m` when `m + 2 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_laplacian {g : E → ℝ} {n m : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hmn : m + 2 ≤ n) :
    ContDiff ℝ m (Laplacian.laplacian g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by simp) hmn
  rw [laplacian_eq_fun_sum (hg.of_le h2)]
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_fderiv_apply (contDiff_fderiv_apply hg ?_ _) le_rfl _
  calc m + 1 + 1 = m + 2 := by rw [add_assoc]; norm_num
    _ ≤ n := hmn
end StdBasis
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
/-- Regularity of the weighted Laplacian: a `C^{n+1}` potential and `C^{n+2}` data give a `C^n`
weighted Laplacian. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_weightedLaplacian {n p q : WithTop ℕ∞} {U f : E → ℝ} (hU : ContDiff ℝ p U)
    (hf : ContDiff ℝ q f) (hp : n + 1 ≤ p) (hq : n + 2 ≤ q) :
    ContDiff ℝ n (weightedLaplacian U f) := by
  have hnq : n + 1 ≤ q :=
    le_trans (by gcongr; norm_num : n + (1 : WithTop ℕ∞) ≤ n + 2) hq
  exact ContDiff.sub (contDiff_laplacian hf hq)
    (ContDiff.inner ℝ (contDiff_gradient hU hp) (contDiff_gradient hf hnq))
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
/-- Regularity of the carré du champ: `C^{n+1}` data give a `C^n` carré du champ. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma {n p q : WithTop ℕ∞} {f g : E → ℝ} (hf : ContDiff ℝ p f)
    (hg : ContDiff ℝ q g) (hp : n + 1 ≤ p) (hq : n + 1 ≤ q) : ContDiff ℝ n (gamma f g) :=
  ContDiff.inner ℝ (contDiff_gradient hf hp) (contDiff_gradient hg hq)
/-- The carré du champ inherits the compact support of its first argument. -/
theorem FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left {f : E → ℝ} (g : E → ℝ) (hfc : HasCompactSupport f) :
    HasCompactSupport (gamma f g) := by
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [gamma_apply, h0]
/-- The carré du champ of two `C¹` functions is continuous. -/
theorem FunctionalInequalities.Analysis.BakryEmery.continuous_gamma {f g : E → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Continuous (gamma f g) :=
  (continuous_gradient hf).inner (continuous_gradient hg)
variable [FiniteDimensional ℝ E]
end Gamma
end
end
end
end
end

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- `D²φ(x)(u, v) = ⟪∇²φ(x) u, v⟫` (the same identity as `Probability.Stein.hessian_eq_inner_fderiv_gradient`,
restated for the operator; the Hessian–Stein chain source is credited). -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x u v : E) :
    bilinearIteratedFDerivTwo ℝ φ x u v = ⟪hessianOperator φ x u, v⟫ := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  have hfun : (fun x : E => fderiv ℝ φ x v) = fun x => ⟪gradient φ x, v⟫ := by
    funext x
    exact inner_gradient_left.symm
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hφ, hfun,
    fderiv_inner_apply ℝ (hg.differentiable one_ne_zero x) (differentiableAt_const v)]
  simp [hessianOperator]
end
end
end
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
end
end

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
private lemma FunctionalInequalities.Analysis.BakryEmery.compact_norm_bound
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {g : X → F} (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hg).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC (g x) ⟨x, rfl⟩).trans (le_max_left _ _)
section Helpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.continuous_hessian_square {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (hessianSqStdBasis f) := by
  classical
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun _ _ =>
      (((hf.fderiv_right (m := 1) (by decide)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const |>.clm_apply continuous_const).pow 2
omit [CompleteSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.compact_hessian_square {f : E → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (hessianSqStdBasis f) := by
  classical
  refine ((hc.fderiv ℝ).fderiv ℝ).mono ?_
  intro x hx hz
  exact hx (by simp [hessianSqStdBasis, bilinearIteratedFDerivTwo, hz])
private lemma FunctionalInequalities.Analysis.BakryEmery.laplacian_perturbation_bound (U V g : E → ℝ) (x : E) {C : ℝ}
    (hC : ‖gradient V x - gradient U x‖ ≤ C) :
    ‖weightedLaplacian V g x‖ ≤
      ‖weightedLaplacian U g x‖ + C * ‖gradient g x‖ := by
  have he :
      weightedLaplacian V g x =
        weightedLaplacian U g x -
          ⟪gradient V x - gradient U x, gradient g x⟫ := by
    simp only [weightedLaplacian_apply, inner_sub_left]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add le_rfl
      ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _))))
variable [MeasurableSpace E] [BorelSpace E]
/-- Keep the integration measure fixed while varying the smooth potential in Γ₂. -/
private lemma FunctionalInequalities.Analysis.BakryEmery.mixed_integral_identity {U V f : E → ℝ}
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x, hessianSqStdBasis f x +
        ⟪fderiv ℝ (gradient V) x (gradient f x), gradient f x⟫
        ∂((volume : Measure E).tilted (-U))) =
      (∫ x, weightedLaplacian V (gamma f f) x
        ∂((volume : Measure E).tilted (-U))) / 2 +
      ∫ x, weightedLaplacian U f x * weightedLaplacian V f x
        ∂((volume : Measure E).tilted (-U)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by decide)
  have ha : ContDiff ℝ 2 (gamma f f) :=
    contDiff_gamma hf3 hf3 (by norm_num) (by norm_num)
  have haC := hasCompactSupport_gamma_left f hc
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hLV : ContDiff ℝ 1 (weightedLaplacian V f) :=
    contDiff_weightedLaplacian hV hf3 (by norm_num) (by norm_num)
  have hiQ : Integrable (weightedLaplacian V (gamma f f))
      ((volume : Measure E).tilted (-U)) :=
    (continuous_weightedLaplacian hV1 ha).integrable_of_hasCompactSupport
      (hasCompactSupport_weightedLaplacian V haC)
  have hiB : Integrable (gamma f (weightedLaplacian V f))
      ((volume : Measure E).tilted (-U)) :=
    (continuous_gamma hf1 hLV).integrable_of_hasCompactSupport
      (hasCompactSupport_gamma_left (weightedLaplacian V f) hc)
  have hibp :
      (∫ x, gamma f (weightedLaplacian V f) x
        ∂((volume : Measure E).tilted (-U))) =
      -(∫ x, weightedLaplacian U f x * weightedLaplacian V f x
        ∂((volume : Measure E).tilted (-U))) := by
    calc
      _ = ∫ x, -weightedLaplacian U f x * weightedLaplacian V f x
          ∂((volume : Measure E).tilted (-U)) :=
        integral_inner_gradient_tilted volume hU hf2 hc hLV
      _ = _ := by simp only [neg_mul, integral_neg]
  calc
    _ = ∫ x, weightedLaplacian V (gamma f f) x / 2 -
        gamma f (weightedLaplacian V f) x
        ∂((volume : Measure E).tilted (-U)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        have he := gammaTwo_eq_hessianSqStdBasis_add_408915f hV hf3 x
        rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hV] at he
        exact he.symm
    _ = _ := by
      rw [integral_sub (hiQ.div_const 2) hiB, integral_div, hibp]
      ring
end Helpers
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Bochner identity for a Lipschitz potential with Lipschitz gradient** (weak Letwin route,
Brascamp–Lieb at `C^{1,1}`): for `U ∈ C¹` Lipschitz with `G`-Lipschitz gradient and integrable
`e^{-U}`, and `f ∈ C_c^∞`, `∫ (ℒf)² dν = ∫ (‖∇²f‖² + ⟪D(∇U) ∇f, ∇f⟫) dν` with `ν = e^{-U} dx`
normalized, `ℒf = Δf − ⟪∇U, ∇f⟫`, and `D(∇U)` the a.e. derivative of the Lipschitz map `∇U`. -/
theorem solution {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) =
      ∫ x, (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x + ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
        ∂((volume : Measure E).tilted (-U)) := by
  classical
  have _hL := hL
  have _hexp := hexp
  obtain ⟨V, hV, he, hVG, _, hD⟩ :=
    FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_408915f hU hG
  let μ : Measure E := (volume : Measure E).tilted (-U)
  let a : E → ℝ := FunctionalInequalities.Analysis.BakryEmery.gamma f f
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by decide)
  have ha2 : ContDiff ℝ 2 a :=
    FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma hf3 hf3 (by norm_num) (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha2.of_le (by norm_num)
  have hac : HasCompactSupport a := FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left f hfc
  have hgf : Continuous (gradient f) := FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hf1
  have hga : Continuous (gradient a) := FunctionalInequalities.Analysis.BakryEmery.continuous_gradient ha1
  have hLf : Continuous (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f) :=
    FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU hf2
  have hLa : Continuous (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U a) :=
    FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU ha2
  have hS : Continuous (FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f) := continuous_hessian_square hf
  obtain ⟨B, hB0, hB⟩ := compact_norm_bound hgf (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hfc)
  obtain ⟨D, hD0, hDb⟩ := compact_norm_bound hga (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hac)
  obtain ⟨M, hM0, hM⟩ :=
    compact_norm_bound hLf (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U hfc)
  obtain ⟨N, hN0, hN⟩ :=
    compact_norm_bound hLa (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U hac)
  obtain ⟨S, hS0, hSb⟩ := compact_norm_bound hS (compact_hessian_square hfc)
  have herror (k : ℕ) (x : E) :
      ‖gradient (V k) x - gradient U x‖ ≤ (G : ℝ) :=
    (he k x).trans (div_le_self G.coe_nonneg (by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith))
  have hgradlim (x : E) :
      Tendsto (fun k => gradient (V k) x) atTop (𝓝 (gradient U x)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm (fun k => he k x)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (G : ℝ)
    simpa only [mul_zero, mul_one_div] using ht
  have hLVlim (g : E → ℝ) (x : E) :
      Tendsto (fun k => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian (V k) g x) atTop
        (𝓝 (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U g x)) := by
    exact tendsto_const_nhds.sub ((hgradlim x).inner tendsto_const_nhds)
  have hLVf (k : ℕ) (x : E) :
      ‖FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian (V k) f x‖ ≤ M + (G : ℝ) * B := by
    exact (laplacian_perturbation_bound U (V k) f x (herror k x)).trans
      (add_le_add (hM x) (mul_le_mul_of_nonneg_left (hB x) G.coe_nonneg))
  have hLVa (k : ℕ) (x : E) :
      ‖FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian (V k) a x‖ ≤ N + (G : ℝ) * D := by
    exact (laplacian_perturbation_bound U (V k) a x (herror k x)).trans
      (add_le_add (hN x) (mul_le_mul_of_nonneg_left (hDb x) G.coe_nonneg))
  have hQ :
      Tendsto (fun k => ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian (V k) a x ∂μ) atTop
        (𝓝 (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U a x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => N + (G : ℝ) * D)
    · intro k
      exact (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian ((hV k).of_le (by decide))
        ha2).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall (hLVa k)
    · exact Eventually.of_forall (hLVlim a)
  have hP :
      Tendsto
        (fun k => ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian (V k) f x ∂μ)
        atTop (𝓝 (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => M * (M + (G : ℝ) * B))
    · intro k
      exact (hLf.mul
        (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian ((hV k).of_le (by decide))
          hf2)).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      apply Eventually.of_forall
      intro x
      rw [norm_mul]
      exact mul_le_mul (hM x) (hLVf k x) (norm_nonneg _) hM0
    · apply Eventually.of_forall
      intro x
      simpa only [pow_two] using
        (hLVlim f x).const_mul (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x)
  have hHcont (k : ℕ) :
      Continuous (fun x => FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
        ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫) := by
    have hg : ContDiff ℝ 1 (gradient (V k)) :=
      FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient (hV k) (by decide)
    exact hS.add (((hg.continuous_fderiv one_ne_zero).clm_apply hgf).inner hgf)
  have hHbound (k : ℕ) (x : E) :
      ‖FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫‖ ≤
        S + (G : ℝ) * B * B := by
    have hop : ‖fderiv ℝ (gradient (V k)) x‖ ≤ (G : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ (hVG k)
    have happ :
        ‖fderiv ℝ (gradient (V k)) x (gradient f x)‖ ≤ (G : ℝ) * B :=
      ((fderiv ℝ (gradient (V k)) x).le_opNorm (gradient f x)).trans
        (mul_le_mul hop (hB x) (norm_nonneg _) G.coe_nonneg)
    exact (norm_add_le _ _).trans
      (add_le_add (hSb x)
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul happ (hB x) (norm_nonneg _) (mul_nonneg G.coe_nonneg hB0))))
  have hDμ :
      ∀ᵐ x ∂μ, Tendsto (fun k => fderiv ℝ (gradient (V k)) x) atTop
        (𝓝 (fderiv ℝ (gradient U) x)) :=
    (tilted_absolutelyContinuous (volume : Measure E) (-U)).ae_le hD
  have hH :
      Tendsto
        (fun k => ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫ ∂μ)
        atTop
        (𝓝 (∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => S + (G : ℝ) * B * B)
    · intro k
      exact (hHcont k).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall (hHbound k)
    · filter_upwards [hDμ] with x hx
      have hev :
          Continuous (fun A : E →L[ℝ] E => A (gradient f x)) :=
        continuous_id.clm_apply continuous_const
      exact tendsto_const_nhds.add
        (((hev.tendsto _).comp hx).inner tendsto_const_nhds)
  have hzero : ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U a x ∂μ = 0 := by
    have hi :=
      FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted (volume : Measure E)
        (U := U) (f := a) (g := fun _ : E => (1 : ℝ))
        hU ha2 hac (contDiff_const (c := (1 : ℝ)))
    simp only [gradient_fun_const, inner_zero_right, integral_zero,
      mul_one, integral_neg] at hi
    exact neg_eq_zero.mp hi.symm
  have hlimit :
      Tendsto
        (fun k => ∫ x, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
          ⟪fderiv ℝ (gradient (V k)) x (gradient f x), gradient f x⟫ ∂μ)
        atTop (𝓝 (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U f x ^ 2 ∂μ)) := by
    have ht := (hQ.div_const 2).add hP
    rw [hzero, zero_div, zero_add] at ht
    apply ht.congr
    intro k
    exact (mixed_integral_identity hU ((hV k).of_le (by decide)) hf hfc).symm
  exact tendsto_nhds_unique hlimit hH
