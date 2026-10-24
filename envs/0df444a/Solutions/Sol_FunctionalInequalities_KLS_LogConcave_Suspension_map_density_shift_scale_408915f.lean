-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:58:25.051045+00:00
-- url     : https://prove2.me/submissions/a12b599c-cfa7-4e77-9047-805ffe30b2e9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- Pushing a density through a measurable equivalence: the new density is the old one composed with
the inverse. -/
theorem FunctionalInequalities.Probability.map_withDensity_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (w : A → ENNReal) (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hw (show Measurable (fun x => φ (e x)) from hφ.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e) (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable) hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => w (e.symm y) * φ y) from (hw.comp e.symm.measurable).mul hφ) e.measurable]
  simp only [e.symm_apply_apply]
end MeasurableSpace
end TiltTransport
end
end
end

open MeasureTheory FunctionalInequalities.Probability.Line
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- **Push-forward under the fibrewise shear** `(a, η) ↦ (a, (F a + η)/σ)`: a density `w` on
`μ ⊗ ds` becomes `|σ| · w(a, σ s - F a)`, the inverse Jacobian of the shear. -/
 theorem solution {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SFinite μ] (F : A → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0)
    (w : A × ℝ → ENNReal) (hw : Measurable w) :
    ((μ.prod volume).withDensity w).map (fun p => (p.1, (F p.1 + p.2) / σ)) =
      (μ.prod volume).withDensity
        (fun p => ENNReal.ofReal |σ| * w (p.1, σ * p.2 - F p.1)) := by
  let e : A × ℝ ≃ᵐ A × ℝ :=
    { toFun p := (p.1, (F p.1 + p.2) / σ)
      invFun p := (p.1, σ * p.2 - F p.1)
      left_inv p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      right_inv p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      measurable_toFun := measurable_fst.prodMk
        (((hF.comp measurable_fst).add measurable_snd).div_const σ)
      measurable_invFun := measurable_fst.prodMk
        ((measurable_const.mul measurable_snd).sub (hF.comp measurable_fst)) }
  have hshift : MeasurePreserving (fun p : A × ℝ => (p.1, F p.1 + p.2))
      (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product
      ((hF.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun x => map_add_left_eq_self volume (F x))
  have hreal : (volume : Measure ℝ).map (fun x => x / σ) =
      ENNReal.ofReal |σ| • volume := by
    simpa only [inv_inv, mul_comm, div_eq_mul_inv] using
      (Real.map_volume_mul_left (inv_ne_zero hσ))
  have hscale : (μ.prod volume).map (fun p : A × ℝ => (p.1, p.2 / σ)) =
      ENNReal.ofReal |σ| • μ.prod volume := by
    change (μ.prod volume).map (Prod.map id (fun x => x / σ)) = _
    rw [← Measure.map_prod_map μ volume measurable_id
      (show Measurable (fun x : ℝ => x / σ) from measurable_id.div_const σ),
      Measure.map_id, hreal, Measure.prod_smul_right]
  have hbase : (μ.prod volume).map e = ENNReal.ofReal |σ| • μ.prod volume := by
    change (μ.prod volume).map
      ((fun p : A × ℝ => (p.1, p.2 / σ)) ∘ (fun p : A × ℝ => (p.1, F p.1 + p.2))) = _
    rw [← Measure.map_map
      (measurable_fst.prodMk (measurable_snd.div_const σ)) hshift.measurable,
      hshift.map_eq, hscale]
  change ((μ.prod volume).withDensity w).map e = _
  rw [FunctionalInequalities.Probability.map_withDensity_measurableEquiv e (μ.prod volume) w hw, hbase, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal |σ|)
      (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable)]
  rfl
