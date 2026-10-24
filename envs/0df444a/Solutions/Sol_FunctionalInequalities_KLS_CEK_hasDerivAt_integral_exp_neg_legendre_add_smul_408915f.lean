-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.hasDerivAt_integral_exp_neg_legendre_add_smul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:36:55.978764+00:00
-- url     : https://prove2.me/submissions/6801499e-30d3-4f10-8297-791138d282d3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_hasDerivAt_legendre_add_smul_of_dualDifferentiable_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_finite_curve_408915f

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem FunctionalInequalities.Analysis.continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc
/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem FunctionalInequalities.Analysis.lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)
end
end
end
end

noncomputable section
open MeasureTheory Set Metric
open scoped Topology
open FunctionalInequalities.Analysis
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities.KLS.CEK in
/-- **First variation of the partition function of the conjugate** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, proof of Theorem 2, first variation (42) integrated; weak Letwin route): for a proper lower semicontinuous potential `q` whose conjugate `ψ = q*` is real, Lipschitz
and has integrable `e^{-ψ}`, and a bounded continuous perturbation `b`, the map
`t ↦ ∫ exp(−(q + t b)*(x)) dx` is differentiable at `0` with derivative
`∫ exp(−ψ(x)) b(∇ψ(x)) dx` (`∇ψ` is the a.e. gradient of the Lipschitz function `ψ`). -/
theorem solution (q : E → EReal) (hq : FunctionalInequalities.Analysis.ProperPotential q)
    (hlsc : LowerSemicontinuous q) (ψ : E → ℝ) (hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal))
    {L : NNReal} (hlip : LipschitzWith L ψ)
    (hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E))
    (b : E → ℝ) (hb : Continuous b) {M : ℝ} (hM : ∀ z, |b z| ≤ M) :
    HasDerivAt
      (fun t : ℝ => ∫ x, Real.exp (-(FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
        ∂(volume : Measure E))
      (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0 := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (b 0)) (hM 0)
  have htop : ∀ x, FunctionalInequalities.Analysis.legendre q x ≠ ⊤ := by
    intro x
    rw [hψ x]
    simp
  have hreal : (fun x => (FunctionalInequalities.Analysis.legendre q x).toReal) = ψ := by
    funext x
    have hx := congrArg EReal.toReal (hψ x)
    simpa using hx
  have hleg_meas : Measurable (FunctionalInequalities.Analysis.legendre q) :=
    (FunctionalInequalities.Analysis.lowerSemicontinuous_legendre q).measurable
  have hψ_meas : Measurable ψ := by
    rw [← hreal]
    exact hleg_meas.ereal_toReal
  have hgradient_meas : Measurable (gradient ψ) := by
    change
      Measurable
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x))
    exact
      (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
        (measurable_fderiv ℝ ψ)
  let F : ℝ → E → ℝ := fun t x =>
    Real.exp (-(FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
  let F' : E → ℝ := fun x => Real.exp (-ψ x) * b (gradient ψ x)
  let bound : E → ℝ := fun x => M * Real.exp M * Real.exp (-ψ x)
  have hF_meas :
      ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (volume : Measure E) := by
    filter_upwards [] with t
    apply
      ((Real.continuous_exp.comp continuous_neg).measurable.comp
        ((FunctionalInequalities.Analysis.lowerSemicontinuous_legendre
          (fun z => q z + ((t * b z : ℝ) : EReal))).measurable.ereal_toReal)).aestronglyMeasurable
  have hF_int : Integrable (F 0) (volume : Measure E) := by
    have hzero : F 0 = fun x => Real.exp (-ψ x) := by
      funext x
      simp [F, hψ x]
    rw [hzero]
    exact hint
  have hF'_meas : AEStronglyMeasurable F' (volume : Measure E) := by
    exact
      (((Real.continuous_exp.comp continuous_neg).measurable.comp hψ_meas).aestronglyMeasurable).mul
        ((hb.measurable.comp hgradient_meas).aestronglyMeasurable)
  have hbound_nonneg : ∀ x, 0 ≤ bound x := by
    intro x
    exact
      mul_nonneg (mul_nonneg hM0 (Real.exp_pos M).le) (Real.exp_pos (-ψ x)).le
  have hbound_int : Integrable bound (volume : Measure E) := by
    simpa [bound] using hint.const_mul (M * Real.exp M)
  have hbdd : BddAbove (Set.range fun z : E => |b z|) := by
    refine ⟨M, ?_⟩
    rintro y ⟨z, rfl⟩
    exact hM z
  have h_lipsch :
      ∀ᵐ x ∂(volume : Measure E),
        LipschitzOnWith (Real.nnabs (bound x)) (F · x) (ball (0 : ℝ) 1) := by
    filter_upwards [] with x
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    let P : ℝ → ℝ :=
      fun t => (FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal
    have hu_abs : |u| ≤ 1 := by
      have hu' : dist u 0 < 1 := hu
      simpa [Real.dist_eq] using hu'.le
    have hv_abs : |v| ≤ 1 := by
      have hv' : dist v 0 < 1 := hv
      simpa [Real.dist_eq] using hv'.le
    have hu_curve :=
      FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_408915f q hq x (htop x) b M hM0 hM u
    have hv_curve :=
      FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_408915f q hq x (htop x) b M hM0 hM v
    have hproper_v :
        FunctionalInequalities.Analysis.ProperPotential (fun z => q z + ((v * b z : ℝ) : EReal)) := by
      refine ⟨?_, ?_⟩
      · intro z
        change q z + ((v * b z : ℝ) : EReal) ≠ ⊥
        intro hzbot
        have hz' : q z + ((v * b z : ℝ) : EReal) = ⊥ := hzbot
        rw [EReal.add_eq_bot_iff] at hz'
        rcases hz' with hzq | hzv
        · exact (hq.1 z) hzq
        · exact EReal.coe_ne_bot (v * b z) hzv
      · obtain ⟨z, hz⟩ := hq.2
        refine ⟨z, ?_⟩
        exact EReal.add_ne_top hz (EReal.coe_ne_top (v * b z))
    have hv_top :
        FunctionalInequalities.Analysis.legendre (fun z => q z + ((v * b z : ℝ) : EReal)) x ≠ ⊤ :=
      hv_curve.1
    have huv_curve :=
      FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_408915f
        (fun z => q z + ((v * b z : ℝ) : EReal)) hproper_v x hv_top b M hM0 hM (u - v)
    have hfun :
        (fun z : E =>
            q z + ((v * b z : ℝ) : EReal) +
              (((u - v) * b z : ℝ) : EReal)) =
          (fun z : E => q z + ((u * b z : ℝ) : EReal)) := by
      funext z
      have hsum :
          ((v * b z : ℝ) : EReal) + (((u - v) * b z : ℝ) : EReal) =
            ((u * b z : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
      rw [add_assoc, hsum]
    have hdiff : |P u - P v| ≤ M * |u - v| := by
      have h := huv_curve.2.2
      change
        |(FunctionalInequalities.Analysis.legendre
              (fun z : E =>
                q z + ((v * b z : ℝ) : EReal) +
                  (((u - v) * b z : ℝ) : EReal)) x).toReal -
            (FunctionalInequalities.Analysis.legendre (fun z => q z + ((v * b z : ℝ) : EReal)) x).toReal| ≤
          |u - v| * M at h
      rw [hfun] at h
      simpa [P, mul_comm] using h
    have hu_shift : |P u - ψ x| ≤ M := by
      calc
        |P u - ψ x| ≤ |u| * M := by
          simpa [P, hψ x] using hu_curve.2.2
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hu_abs hM0
        _ = M := one_mul M
    have hv_shift : |P v - ψ x| ≤ M := by
      calc
        |P v - ψ x| ≤ |v| * M := by
          simpa [P, hψ x] using hv_curve.2.2
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hv_abs hM0
        _ = M := one_mul M
    have hu_neg_mem :
        -P u ∈ Icc (-(ψ x + M)) (-(ψ x - M)) := by
      rcases abs_le.mp hu_shift with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hv_neg_mem :
        -P v ∈ Icc (-(ψ x + M)) (-(ψ x - M)) := by
      rcases abs_le.mp hv_shift with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hexp :=
      (convex_Icc (-(ψ x + M)) (-(ψ x - M))).norm_image_sub_le_of_norm_deriv_le
        (fun y hy => (Real.hasDerivAt_exp y).differentiableAt)
        (fun y hy => by
          rw [Real.deriv_exp, Real.norm_eq_abs, Real.abs_exp]
          exact Real.exp_le_exp.2 hy.2)
        hu_neg_mem hv_neg_mem
    have hexp' :
        |Real.exp (-P u) - Real.exp (-P v)| ≤
          Real.exp (-(ψ x - M)) * |P u - P v| := by
      calc
        |Real.exp (-P u) - Real.exp (-P v)| =
            ‖Real.exp (-P v) - Real.exp (-P u)‖ := by
              rw [Real.norm_eq_abs, abs_sub_comm]
        _ ≤ Real.exp (-(ψ x - M)) * ‖-P v - -P u‖ := hexp
        _ = Real.exp (-(ψ x - M)) * |P u - P v| := by
          congr 1
          rw [show -P v - -P u = P u - P v by ring]
          rw [Real.norm_eq_abs]
    have hcoeff :
        Real.exp (-(ψ x - M)) = Real.exp (-ψ x) * Real.exp M := by
      rw [show -(ψ x - M) = -ψ x + M by ring, Real.exp_add]
    have hmain : dist (F u x) (F v x) ≤ bound x * dist u v := by
      calc
        dist (F u x) (F v x) =
            |Real.exp (-P u) - Real.exp (-P v)| := by
              simp [F, P, Real.dist_eq]
        _ ≤ Real.exp (-(ψ x - M)) * |P u - P v| := hexp'
        _ ≤ Real.exp (-(ψ x - M)) * (M * |u - v|) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = bound x * dist u v := by
          rw [hcoeff]
          simp [bound, Real.dist_eq]
          ring
    have hcoef : (↑(Real.nnabs (bound x)) : ℝ) = bound x := by
      rw [Real.nnabs_of_nonneg (hbound_nonneg x), Real.coe_toNNReal]
      exact hbound_nonneg x
    rw [hcoef]
    exact hmain
  have h_diff :
      ∀ᵐ x ∂(volume : Measure E), HasDerivAt (F · x) (F' x) 0 := by
    filter_upwards [hlip.ae_differentiableAt] with x hx
    have hdual :
        DifferentiableAt ℝ (fun y => (FunctionalInequalities.Analysis.legendre q y).toReal) x := by
      rw [hreal]
      exact hx
    have hyint :
        x ∈ interior {y : E | FunctionalInequalities.Analysis.legendre q y ≠ ⊤} := by
      have hset : {y : E | FunctionalInequalities.Analysis.legendre q y ≠ ⊤} = (univ : Set E) := by
        ext y
        simp [htop y]
      rw [hset]
      simp
    have hv :=
      FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_408915f
        q hq hlsc x hyint hdual b hb hbdd
    rw [hreal] at hv
    have hneg := hv.neg
    convert hneg.exp using 1 <;> simp [F, F', hψ x]
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_lip
      (F := F) (F' := F') (bound := bound) (x₀ := (0 : ℝ))
      (s := ball (0 : ℝ) 1)
      (ball_mem_nhds (0 : ℝ) zero_lt_one)
      hF_meas hF_int hF'_meas h_lipsch hbound_int h_diff
  dsimp [F, F'] at hresult ⊢
  exact hresult.2
