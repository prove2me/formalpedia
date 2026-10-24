-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convolution_hessian_integral_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:24:25.734289+00:00
-- url     : https://prove2.me/submissions/c3d1ebb1-e629-499d-96ac-fb63a2a6e5af

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
import Theorems.Thm_FunctionalInequalities_Analysis_expansion_secondDifference_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hessianMatrix_quadratic_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_local_taylor_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_tendsto_integral_secondDifference_mul_408915f

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12C2TaylorHessianBound
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- **Second-order Taylor bound with the coordinate Hessian** (weak Letwin route, viscosity tests):
for `ψ` twice differentiable at `x₀` (`ContDiffAt ℝ 2`), every `ε > 0` admits `r > 0` with
`|ψ x − ψ x₀ − Dψ(x₀)(x − x₀) − ½ ⟪x − x₀, ∇²ψ(x₀)(x − x₀)⟫| ≤ ε ‖x − x₀‖²` on `ball x₀ r`. -/
theorem FunctionalInequalities.Analysis.exists_taylor_two_hessianMatrix_bound {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin (hessianMatrix ψ x₀) (x - x₀)⟫)| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  rcases local_taylor_two_408915f hψ hε with ⟨r, hr, hrbound⟩
  refine ⟨r, hr, ?_⟩
  intro x hx
  rw [hessianMatrix_quadratic_408915f]
  exact hrbound x hx
end
end
end LT12C2TaylorHessianBound
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
private lemma FunctionalInequalities.Analysis.smooth_secondDifference {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ContDiff ℝ 2 w)
    (x v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin (hessianMatrix w x) v⟫) := by
  apply expansion_secondDifference_408915f
    (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ w x))
  intro ε hε
  obtain ⟨r, hr, hb⟩ := exists_taylor_two_hessianMatrix_bound hw.contDiffAt hε
  filter_upwards [ball_mem_nhds x hr] with y hy
  simpa only [quadraticAt, InnerProductSpace.toDual_symm_apply] using hb y hy
private lemma FunctionalInequalities.Analysis.convolution_shift {n : ℕ}
    (ρ u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x a : EuclideanSpace ℝ (Fin n)) :
    (∫ y, u (y + a) * ρ (x - y)) =
      convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + a) := by
  rw [← integral_sub_left_eq_self (fun y => u (y + a) * ρ (x - y)) volume x]
  unfold convolution
  apply integral_congr_ae
  filter_upwards [] with y
  have he : x - y + a = x + a - y := by abel
  simp only [sub_sub_cancel, he, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm _ _
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hu : Continuous u)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin
      (FunctionalInequalities.Probability.Stein.hessianMatrix (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v⟫ =
      ∫ y, u y * iteratedFDeriv ℝ 2 (fun z => ρ (x - z)) y (fun _ => v) := by
  let χ := fun y => ρ (x - y)
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hi (a : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => u (y + a) * χ y) volume := by
    have hc : Continuous (fun y => u (y + a) * χ y) :=
      (hu.comp (continuous_id.add continuous_const)).mul hχ.continuous
    exact hc.integrable_of_hasCompactSupport hχc.mul_left
  have hi₀ : Integrable (fun y => u y * χ y) volume := by
    simpa only [add_zero] using hi 0
  have he (t : ℝ) :
      (∫ y, (u (y + t • v) + u (y - t • v) - 2 * u y) / t ^ 2 * χ y) =
        (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2 := by
    have him : Integrable (fun y => u (y - t • v) * χ y) volume := by
      simpa only [neg_smul, ← sub_eq_add_neg] using hi ((-t) • v)
    have hip : Integrable
        (fun y => u (y + t • v) * χ y + u (y - t • v) * χ y) volume :=
      (hi (t • v)).add him
    calc
      _ = (∫ y, ((u (y + t • v) * χ y + u (y - t • v) * χ y) -
          2 * (u y * χ y)) / t ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = ((∫ y, u (y + t • v) * χ y) +
          (∫ y, u (y - t • v) * χ y) -
          2 * (∫ y, u y * χ y)) / t ^ 2 := by
        rw [integral_div,
          integral_sub
            (f := fun y => u (y + t • v) * χ y + u (y - t • v) * χ y)
            (g := fun y => 2 * (u y * χ y)) hip (hi₀.const_mul 2),
          integral_add
            (f := fun y => u (y + t • v) * χ y)
            (g := fun y => u (y - t • v) * χ y) (hi (t • v)) him,
          integral_const_mul]
      _ = _ := by
        have he₁ := convolution_shift ρ u x (t • v)
        have he₂ := convolution_shift ρ u x (-(t • v))
        have he₀ := convolution_shift ρ u x 0
        simpa only [χ, w, add_zero, ← sub_eq_add_neg] using
          congrArg (fun p : ℝ × ℝ × ℝ => (p.1 + p.2.1 - 2 * p.2.2) / t ^ 2)
            (show
              ((∫ y, u (y + t • v) * ρ (x - y)),
                (∫ y, u (y + -(t • v)) * ρ (x - y)),
                (∫ y, u (y + 0) * ρ (x - y))) =
              (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + t • v),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + -(t • v)),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + 0)) from
              by rw [he₁, he₂, he₀])
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  exact tendsto_nhds_unique (smooth_secondDifference hw x v)
    ((FunctionalInequalities.Analysis.tendsto_integral_secondDifference_mul_408915f hu hχ hχc v).congr he)
