-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hessianMatrix_quadraticAt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:22:31.277273+00:00
-- url     : https://prove2.me/submissions/d4caa2d1-17ae-4dee-858e-cc40260b572f

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
section LT12E1AlexandrovPointEquation
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
/-- `quadraticAt A x₀ b c` is smooth (weak Letwin route). -/
theorem FunctionalInequalities.Analysis.contDiff_quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) : ContDiff ℝ 2 (quadraticAt A x₀ b c) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  change ContDiff ℝ 2
    (fun x => c + ⟪b, x - x₀⟫ + (1 / 2 : ℝ) * ⟪x - x₀, T (x - x₀)⟫)
  exact (contDiff_const.add
    (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).inner ℝ
      (T.contDiff.comp (contDiff_id.sub contDiff_const))))
private lemma FunctionalInequalities.Analysis.quadraticAt_fderiv_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (y w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (quadraticAt A x₀ b c) y w =
      ⟪b, w⟫ + (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀
  have ht := T.hasFDerivAt.comp y hd
  have hb := (hasFDerivAt_const (𝕜 := ℝ) b y).inner ℝ hd
  have hq := hd.inner ℝ ht
  have hh := (hb.const_add c).add (hq.const_mul (1 / 2 : ℝ))
  change HasFDerivAt (quadraticAt A x₀ b c) _ y at hh
  rw [hh.fderiv]
  simp [fderivInnerCLM_apply, T]
private lemma FunctionalInequalities.Analysis.quadraticAt_second_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ w x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
      (fun y => (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫)) x v =
      (1 / 2 : ℝ) *
        (⟪v, Matrix.toEuclideanLin A w⟫ + ⟪w, Matrix.toEuclideanLin A v⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
  have ht := T.hasFDerivAt.comp x hd
  have h₁ := hd.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) (T w) x)
  have h₂ := (hasFDerivAt_const (𝕜 := ℝ) w x).inner ℝ ht
  have hh := (h₁.add h₂).const_mul (1 / 2 : ℝ)
  simpa [fderivInnerCLM_apply, T, mul_add] using
    congrArg (fun L => L v) hh.fderiv
private lemma FunctionalInequalities.Analysis.quadraticAt_basis_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Matrix.toLpLin_apply 2 2]
  simp [Matrix.mulVec, dotProduct]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The coordinate Hessian of `quadraticAt A x₀ b c` is `A` at every point when `A` is symmetric
(weak Letwin route). -/
theorem solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Probability.Stein.hessianMatrix (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) x = A := by
  ext i j
  change bilinearIteratedFDerivTwo ℝ (FunctionalInequalities.Analysis.quadraticAt A x₀ b c) x
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) = A i j
  rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
    (FunctionalInequalities.Analysis.contDiff_quadraticAt A x₀ b c)]
  simp_rw [quadraticAt_fderiv_apply]
  rw [fderiv_const_add, quadraticAt_second_apply,
    quadraticAt_basis_entry, quadraticAt_basis_entry]
  have hs : A j i = A i j := by simpa using hA.apply i j
  rw [hs]
  ring
