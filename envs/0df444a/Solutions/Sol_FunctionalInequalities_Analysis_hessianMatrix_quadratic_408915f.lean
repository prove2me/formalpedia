-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hessianMatrix_quadratic_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:14:23.247896+00:00
-- url     : https://prove2.me/submissions/ffd6d2a6-e159-41cb-b0d0-ced4eb0bdbb2

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
private lemma FunctionalInequalities.Analysis.matrix_quadratic_formula
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin M v⟫ =
      ∑ i, ∑ j, v.ofLp i * (M i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin (FunctionalInequalities.Probability.Stein.hessianMatrix ψ x) v⟫ =
      (fderiv ℝ (fderiv ℝ ψ) x) v v := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x
  let c : Fin n → ℝ := fun i => (b.repr v).ofLp i
  have hv : ∑ i, c i • b i = v := b.sum_repr v
  have hc : ∀ i, c i = v.ofLp i := by
    intro i
    exact (EuclideanSpace.basisFun_repr (Fin n) ℝ v i).symm
  have hentry : ∀ i j, FunctionalInequalities.Probability.Stein.hessianMatrix ψ x i j = H (b i) (b j) := by
    intro i j
    change
      bilinearIteratedFDerivTwo ℝ ψ x (b i) (b j) =
        H (b i) (b j)
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    simpa [H] using iteratedFDeriv_two_apply ψ x ![b i, b j]
  have hfirst :
      H (∑ i, c i • b i) = ∑ i, H (c i • b i) := by
    rw [map_sum]
  have hsecond :
      ∀ i, (H (c i • b i)) (∑ j, c j • b j) =
        ∑ j, (H (c i • b i)) (c j • b j) := by
    intro i
    rw [map_sum]
  have hsum :
      H (∑ i, c i • b i) (∑ j, c j • b j) =
        ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
    calc
      H (∑ i, c i • b i) (∑ j, c j • b j) =
          (∑ i, H (c i • b i)) (∑ j, c j • b j) := by
            rw [hfirst]
      _ = ∑ i, (H (c i • b i)) (∑ j, c j • b j) := by
            rw [sum_apply]
      _ = ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsecond i]
            simp only [map_smul, smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [matrix_quadratic_formula]
  simp_rw [hentry, ← hc]
  rw [← hsum, hv]
