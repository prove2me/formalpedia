-- Prove2me | solution 1 for FunctionalInequalities.Analysis.fderiv_det_updateRow_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:02:46.153641+00:00
-- url     : https://prove2.me/submissions/3cc0b375-b08e-4d11-a6ad-3d07e6eb929d

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz

section
noncomputable section
open scoped Matrix.Norms.Elementwise
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The determinant is differentiable (it is a continuous multilinear map of the rows). -/
theorem FunctionalInequalities.Analysis.differentiableAt_det (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M :=
  (FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).differentiableAt
/-- The derivative of the determinant is the sum of row replacements. -/
theorem FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (FunctionalInequalities.Analysis.detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl
end
end
end
end

noncomputable section
open Matrix
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
 lemma solution
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
  let D : E →L[ℝ] Fin n → Fin n → ℝ :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[ℝ] ℝ)
        else fderiv ℝ (fun y => A y k l) x))
  let B : E → Fin n → Fin n → ℝ :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  have hd :=
    congrArg (fun L : E →L[ℝ] ℝ => L v)
      ((FunctionalInequalities.Analysis.differentiableAt_det (Matrix.of (B x))).hasFDerivAt.comp x hD).fderiv
  change
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
      fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
        (B x) (D v) at hd
  have hdet :=
    FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  change
    fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) =
      ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det at hdet
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  calc
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
          (B x) (D v) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
      rw [hB]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [if_pos rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [if_neg h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv ℝ (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, if_neg h]
        rw [hr]
        rfl
