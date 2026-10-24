-- Prove2me | solution 1 for FunctionalInequalities.Energy.LipschitzGradient.localSlope_holds_of_relaxation_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:59.670647+00:00
-- url     : https://prove2.me/submissions/9db1beb6-144b-47d5-b675-d7815cd5f8b9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- The mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const
/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl
/-- Variance is continuous in `L²`, including at constant functions. -/
theorem FunctionalInequalities.L2.continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
/-- The `NNReal` variance of a pointwise square-integrable function is Mathlib's real variance
converted to `NNReal`; no information is lost because pointwise variance is nonnegative. -/
theorem FunctionalInequalities.L2.variance_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    variance μ (hf.toLp f) =
      (ProbabilityTheory.variance f (μ : Measure α)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg f (μ : Measure α))]
  exact (coe_variance_eq_pointwise μ (hf.toLp f)).trans
    (ProbabilityTheory.variance_congr hf.coeFn_toLp)
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end
end
end

section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Functional
end FunctionalInequalities.Energy.Functional
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Functional
variable {X : Type*}
/-- Coercing a finite energy back to `ENNReal` recovers the original value. -/
@[simp]
theorem FunctionalInequalities.Energy.Functional.coe_finiteValue (energy : Functional X) (x : energy.domain) :
    (energy.finiteValue x : ENNReal) = energy x.1 :=
  ENNReal.coe_toNNReal x.2
end
end
end
end

section
noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
/-- Relaxation never increases the energy of a concrete test. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_toAmbient_le (f : P.Test) :
    P.sequentialRelaxation (P.toAmbient f) ≤ (P.energy f : ENNReal) := by
  refine (P.sequentialRelaxation_le_sequenceEnergy (P.constantSequence f)).trans_eq ?_
  exact liminf_const (P.energy f : ENNReal)
/-- Every realized concrete test has finite relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_finiteAt_toAmbient (f : P.Test) :
    P.sequentialRelaxation.FiniteAt (P.toAmbient f) :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (P.sequentialRelaxation_toAmbient_le f)
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : ProbabilityMeasure E) (m : Measure E)
  [Measure.IsAddHaarMeasure m]
omit sct in
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient_408915f f x hx
omit sct in
/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]
section RealIntegral
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
/-- The literature energy of a locally Lipschitz function with square-integrable gradient is the
real integral of the squared gradient norm, under absolute continuity. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_integral_gradient
    (hac : (ν : Measure V) ≪ m) (f : V → ℝ) (hf : LocallyLipschitz f)
    (hg : MemLp (gradient f) 2 (ν : Measure V)) :
    energy ν f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V)) := by
  rw [energy_eq_lintegral_gradient ν m hac f hf,
    ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hg.1).mp hg)
      (ae_of_all _ fun x ↦ sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
end RealIntegral
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]
section Bridge
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.LipschitzGradient
end FunctionalInequalities.Energy.LipschitzGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LipschitzGradient
namespace FunctionalInequalities.Energy.LipschitzGradient
end FunctionalInequalities.Energy.LipschitzGradient
open FunctionalInequalities.Energy.LipschitzGradient in
/-- A valid constant of the Lipschitz gradient relaxation is a literature constant: approximate a
locally Lipschitz literature test by smooth compactly supported functions in the graph norm. -/
theorem solution (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : FunctionalInequalities.Poincare.L2Energy.Holds ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) C) :
    FunctionalInequalities.Poincare.LocalSlope.Holds ν C := by
  intro f hf
  obtain ⟨hlip, hL2, hgL2⟩ := (FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_408915f ν m hac f).mp hf
  obtain ⟨fs, hfs, hconv, hgconv⟩ :=
    FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2
      ν m hac (ContinuousLinearMap.id ℝ V) f hlip hL2 (by simpa using hgL2)
  have hsL2 (j : ℕ) : MemLp (fs j) 2 (ν : Measure V) := (hfs j).2.2.1
  have hgsL2 (j : ℕ) : MemLp (gradient (fs j)) 2 (ν : Measure V) := by
    simpa using (hfs j).2.2.2
  have hval := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hsL2 f hL2).mpr hconv
  have hgrad := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j ↦ gradient (fs j)) hgsL2 (gradient f) hgL2).mpr (by
      convert! hgconv using 1)
  have hvar : Tendsto (fun j ↦ (FunctionalInequalities.L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ)) atTop
      (𝓝 (FunctionalInequalities.L2.variance ν (hL2.toLp f) : ℝ)) :=
    ((NNReal.continuous_coe.comp (FunctionalInequalities.L2.continuous_variance ν)).tendsto _).comp hval
  have henergy : Tendsto (fun j ↦ ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2) atTop
      (𝓝 (‖hgL2.toLp (gradient f)‖ ^ 2)) :=
    hgrad.norm.pow 2
  have hbound : ∀ j, (FunctionalInequalities.L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ) ≤
      (C : ℝ) * ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2 := by
    intro j
    have htest : FunctionalInequalities.Energy.WeightedGradient.IsTest ν (ContinuousLinearMap.id ℝ V) (fs j) :=
      FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν _ (hfs j).1 (hfs j).2.1
    have hmem : (hsL2 j).toLp (fs j) ∈ (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac).domain :=
      FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν _ hac htest
    have hfin : (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac).FiniteAt ((hsL2 j).toLp (fs j)) :=
      FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_finiteAt_toAmbient
        (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
          FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V))) ⟨_, hmem⟩
    have h1 := h ⟨_, hfin⟩
    have h2 : (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac).finiteValue ⟨_, hfin⟩ ≤
        ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 := by
      apply ENNReal.coe_le_coe.mp
      rw [FunctionalInequalities.Energy.Functional.coe_finiteValue]
      have h3 := FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_toAmbient_le
        (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
          FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V))) ⟨_, hmem⟩
      change (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) ((hsL2 j).toLp (fs j)) ≤
        ((‖FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hmem⟩‖₊ ^ 2 : NNReal) : ENNReal)
        at h3
      rw [FunctionalInequalities.Energy.WeightedGradient.operator_apply ν _ hac hfr htest hmem rfl] at h3
      exact h3
    have h4 : FunctionalInequalities.L2.variance ν ((hsL2 j).toLp (fs j)) ≤ C * ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    have h5 := NNReal.coe_le_coe.mpr h4
    push_cast at h5
    exact h5
  have hreal : (FunctionalInequalities.L2.variance ν (hL2.toLp f) : ℝ) ≤ (C : ℝ) * ‖hgL2.toLp (gradient f)‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hvar (tendsto_const_nhds.mul henergy) hbound
  rw [FunctionalInequalities.L2.variance_toLp, Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _),
    FunctionalInequalities.L2.norm_toLp_sq] at hreal
  rw [← ProbabilityTheory.ofReal_variance hL2,
    FunctionalInequalities.Energy.LocalSlope.energy_eq_integral_gradient ν m hac f hlip hgL2,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal
