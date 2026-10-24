-- Prove2me | solution 1 for FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:36:25.115893+00:00
-- url     : https://prove2.me/submissions/49372c0e-9150-4cc6-a764-4490e18e4d4b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_ae_exists_quadraticAt_expansion_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_penalized_maximum_with_comparison_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_posDef_and_convolution_le_log_det_hessianMatrix_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_posDef_and_det_eq_of_quadratic_expansion_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_penalized_maxima_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_eq_lintegral_of_isOpen_408915f

section
noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D6BAeMongeAmpere
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- **The a.e. Monge–Ampère equation for an Alexandrov solution** (weak Letwin route):
if the subgradient images of the convex `u` on open sets carry a continuous positive density `f`, then at
almost every point `u` has a second-order expansion with a positive definite symmetric `B`, `det B = f x`. -/
theorem FunctionalInequalities.Analysis.ae_exists_posDef_det_eq {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ B.det = f x ∧
        ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_quadraticAt_expansion_408915f hconv] with x hx
  rcases hx with ⟨B, hB, g, hexp⟩
  have hresult : B.PosDef ∧ B.det = f x :=
    posDef_and_det_eq_of_quadratic_expansion_408915f hconv
      (Ω := univ) isOpen_univ
      (fun G hG _ => hMA G hG)
      (mem_univ x) hf.continuousAt (hfpos x) hB hexp
  exact ⟨B, hB, hresult.1, hresult.2, g, hexp⟩
end
end
end LT12D6BAeMongeAmpere
end
end

noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.exists_moment_bumps (n : ℕ) :
    ∃ φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
      Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun k =>
    ContDiffBump.mk
      (1 / (2 * ((k : ℝ) + 1)))
      (1 / ((k : ℝ) + 1))
      (by positivity)
      (by
        have hk : 0 < (k : ℝ) + 1 := by positivity
        apply (div_lt_div_iff₀ (by positivity) hk).2
        nlinarith)
  refine ⟨φ, ?_⟩
  have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro a
    obtain ⟨j, hj⟩ := exists_nat_gt a
    filter_upwards [eventually_ge_atTop j] with k hk
    have hk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hnat
private lemma FunctionalInequalities.Analysis.moment_mollification_contDiff_and_close
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ 2
        (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧
      ∀ x, |convolution (φ.normed volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x| ≤ (L : ℝ) * φ.rOut := by
  constructor
  · exact HasCompactSupport.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.hasCompactSupport_normed φ.contDiff_normed hu.continuous.locallyIntegrable
  · intro x
    rw [← Real.dist_eq]
    apply ContDiffBump.dist_normed_convolution_le hu.continuous.aestronglyMeasurable
    intro y hy
    exact (hu.dist_le_mul y x).trans
      (mul_le_mul_of_nonneg_left (le_of_lt hy) L.coe_nonneg)
private lemma FunctionalInequalities.Analysis.moment_mollification_tendstoLocallyUniformly
    {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Continuous F)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    TendstoLocallyUniformly
      (fun k => convolution ((φ k).normed volume) F
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) F atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hc :
      Tendsto
        (fun i : ℕ × EuclideanSpace ℝ (Fin n) =>
          convolution ((φ i.1).normed volume) F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume i.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (F x)) :=
    ContDiffBump.convolution_tendsto_right
      (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hF.aestronglyMeasurable)
      ((hF.tendsto x).comp tendsto_snd)
      tendsto_snd
  exact (((hF.tendsto x).comp tendsto_snd).prodMk_nhds hc).mono_right
    (nhds_le_uniformity (F x))
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Export the existing moment-map centered-difference estimate with its exact 4/kappa coefficient. -/
theorem solution {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hV : ContDiff ℝ 1 V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hC1 : ContDiff ℝ 1 u) :
    ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by
  classical
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => -u x + V (gradient u x)
  have hgrad : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hC1.continuous_fderiv (by norm_num))
  have hF : Continuous F := hu.continuous.neg.add (hV.continuous.comp hgrad)
  have hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
        volume (FunctionalInequalities.Analysis.subgradientImage u G) =
          ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) := by
    intro G hG
    exact FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f
      hu hconv hnorm hK.isClosed hKc hV.continuous.measurable hmap hG
  obtain ⟨φ, hφ⟩ := exists_moment_bumps n
  let uk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    convolution ((φ k).normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    convolution ((φ k).normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let δ : ℕ → ℝ := fun k => (L : ℝ) * (φ k).rOut
  have huk : ∀ k, ContDiff ℝ 2 (uk k) := fun k =>
    (moment_mollification_contDiff_and_close hu (φ k)).1
  have hclose : ∀ k x, |uk k x - u x| ≤ δ k := fun k =>
    (moment_mollification_contDiff_and_close hu (φ k)).2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using hφ.const_mul (L : ℝ)
  have hFk : TendstoLocallyUniformly Fk F atTop :=
    moment_mollification_tendstoLocallyUniformly hF φ hφ
  have hposlog : ∀ k x,
      (FunctionalInequalities.Probability.Stein.hessianMatrix (uk k) x).PosDef ∧
        Fk k x ≤ Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix (uk k) x).det := by
    intro k x
    apply FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix_408915f hconv hF
    filter_upwards
      [FunctionalInequalities.Analysis.ae_exists_posDef_det_eq hconv (Real.continuous_exp.comp hF)
        (fun y => Real.exp_pos (F y)) hMA] with y hy
    rcases hy with ⟨B, hB, hPD, hdet, hexp⟩
    refine ⟨B, hB, hPD, ?_, hexp⟩
    rw [hdet, Function.comp_apply, Real.log_exp]
  have hint : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  obtain ⟨⟨xm, hm⟩, hcoer⟩ :=
    FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
      volume hconv hint
  have hgrad_bound (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hu)
  obtain ⟨C, hCball⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ))
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_id).continuousOn
  have hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C := by
    intro x
    have hx : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) :=
      mem_closedBall_zero_iff.mpr (hgrad_bound x)
    simpa only [id_eq, Real.norm_eq_abs] using hCball (gradient u x) hx
  have hsd : ∀ x h : EuclideanSpace ℝ (Fin n),
      u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2 := by
    intro x h
    have hmax : ∀ η > 0, ∃ x₀,
        (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
          u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
        V (gradient u (x₀ + h)) - u (x₀ + h) +
          (V (gradient u (x₀ - h)) - u (x₀ - h)) -
          2 * (V (gradient u x₀) - u x₀) ≤ η * (n : ℝ) := by
      intro η hη
      simpa only [F, neg_add_eq_sub] using
        FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_408915f hconv hu hcoer hF hMA huk hδ
          hclose hFk (fun k y => (hposlog k y).1) (fun k y => (hposlog k y).2) h hη
    simpa only [div_mul_eq_mul_div] using
      FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_408915f hconv
        (hC1.differentiable (by norm_num)) (hV.differentiable (by norm_num))
        hκ hstrong hC hm n h hmax x
  exact hsd
