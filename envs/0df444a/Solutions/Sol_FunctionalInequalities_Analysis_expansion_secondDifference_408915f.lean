-- Prove2me | solution 1 for FunctionalInequalities.Analysis.expansion_secondDifference_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:22:56.855032+00:00
-- url     : https://prove2.me/submissions/4a754f31-e7a2-414f-bb8a-99a1dcc769b3

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D8MollifiedLogdetBound
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
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - FunctionalInequalities.Analysis.quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫) := by
  let q := ⟪v, Matrix.toEuclideanLin B v⟫
  have hp (t : ℝ) :
      FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v) =
        u x + t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    have he : x + t • v - x = t • v := by abel
    simp only [FunctionalInequalities.Analysis.quadraticAt, he, map_smul, real_inner_smul_left,
      real_inner_smul_right, q]
    ring
  have hm (t : ℝ) :
      FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v) =
        u x - t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    simpa only [neg_smul, ← sub_eq_add_neg, neg_mul, neg_sq] using hp (-t)
  have htp : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have htm : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x - t • v) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa only [zero_smul, sub_zero] using hc.tendsto 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (4 * (‖v‖ ^ 2 + 1))
  have hd : 0 < 4 * (‖v‖ ^ 2 + 1) := by positivity
  have hη : 0 < η := div_pos hε hd
  have hηeq : η * (4 * (‖v‖ ^ 2 + 1)) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hsmall : 2 * η * ‖v‖ ^ 2 < ε := by
    nlinarith [sq_nonneg ‖v‖]
  filter_upwards [(htp.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    (htm.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with t ht₁ ht₂ ht
  have htpos : 0 < t := ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hnum :
      |(u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q| ≤
        2 * η * t ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = |(u (x + t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v)) +
          (u (x - t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v))| := by
        rw [hp, hm]
        congr 1
        ring
      _ ≤ |u (x + t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v)| +
          |u (x - t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v)| :=
        abs_add_le _ _
      _ ≤ η * ‖x + t • v - x‖ ^ 2 + η * ‖x - t • v - x‖ ^ 2 :=
        add_le_add ht₁ ht₂
      _ = _ := by
        have he₁ : x + t • v - x = t • v := by abel
        have he₂ : x - t • v - x = -(t • v) := by abel
        rw [he₁, he₂, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        ring
  have heq :
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 - q =
        ((u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q) / t ^ 2 := by
    field_simp
  change dist ((u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2) q < ε
  rw [Real.dist_eq, heq, abs_div, abs_of_pos ht2]
  apply (div_lt_iff₀ ht2).mpr
  have hh := mul_lt_mul_of_pos_right hsmall ht2
  nlinarith
