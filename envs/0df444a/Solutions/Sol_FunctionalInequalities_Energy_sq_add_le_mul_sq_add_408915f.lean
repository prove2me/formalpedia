-- Prove2me | solution 1 for FunctionalInequalities.Energy.sq_add_le_mul_sq_add_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:56:29.727996+00:00
-- url     : https://prove2.me/submissions/403cf81e-3d3c-44c1-9b01-16d4149f8192

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section General
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Young's inequality with a parameter, in the real line. -/
theorem FunctionalInequalities.Energy.real_sq_add_le {t a b : ℝ} (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + t⁻¹) * b ^ 2 := by
  have hX : 0 ≤ t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b := by
    have h2 : t * (t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b) = (t * a - b) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (t * a - b), ht]
  nlinarith [hX]
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities.Energy in
/-- Young's inequality with a parameter, in `ℝ≥0∞`, including the infinite values. -/
theorem solution {θ : ℝ≥0} (hθ : 0 < θ) (x y : ℝ≥0∞) :
    (x + y) ^ 2 ≤ (1 + (θ : ℝ≥0∞)) * x ^ 2 + (1 + (θ : ℝ≥0∞)⁻¹) * y ^ 2 := by
  have hθinv : ((θ : ℝ≥0∞))⁻¹ = ((θ⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv hθ.ne').symm
  rw [hθinv]
  rcases eq_or_ne x ⊤ with hx | hx
  · have h1 : (1 + (θ : ℝ≥0∞)) * x ^ 2 = ⊤ := by
      rw [hx, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, top_add]
    exact le_top
  rcases eq_or_ne y ⊤ with hy | hy
  · have h1 : (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * y ^ 2 = ⊤ := by
      rw [hy, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, add_top]
    exact le_top
  obtain ⟨a, rfl⟩ : ∃ a : ℝ≥0, x = (a : ℝ≥0∞) := ⟨x.toNNReal, (ENNReal.coe_toNNReal hx).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ≥0, y = (b : ℝ≥0∞) := ⟨y.toNNReal, (ENNReal.coe_toNNReal hy).symm⟩
  have hnn : (a + b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact FunctionalInequalities.Energy.real_sq_add_le (by exact_mod_cast hθ)
  calc ((a : ℝ≥0∞) + (b : ℝ≥0∞)) ^ 2 = ((((a + b) ^ 2 : ℝ≥0)) : ℝ≥0∞) := by
        rw [ENNReal.coe_pow, ENNReal.coe_add]
    _ ≤ ((((1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 : ℝ≥0)) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hnn
    _ = (1 + (θ : ℝ≥0∞)) * (a : ℝ≥0∞) ^ 2 + (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * (b : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_add,
          ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_pow]
