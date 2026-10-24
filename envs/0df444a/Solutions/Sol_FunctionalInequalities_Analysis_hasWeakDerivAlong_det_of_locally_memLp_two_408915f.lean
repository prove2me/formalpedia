-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:37:56.636767+00:00
-- url     : https://prove2.me/submissions/751d60ae-1ffd-4178-8311-7cc51a1a85f6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
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
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetProd_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_408915f

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
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
/-- The determinant of a bounded weak matrix field has its exact signed
permutation-polynomial directional derivative, locally in L2. -/
theorem solution {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  have hp (σ : Equiv.Perm ι) :=
    FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two_408915f
      (Finset.univ : Finset ι)
      (f := fun i x => A x (σ i) i)
      (df := fun i x => DA x (σ i) i)
      (v := v)
      (fun i _ => hA (σ i) i)
      (fun i _ => hbound (σ i) i)
      (fun i _ => hDA2 (σ i) i)
  have hs :=
    FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_408915f
      (Finset.univ : Finset (Equiv.Perm ι))
      (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ))
      (f := fun σ x => ∏ i : ι, A x (σ i) i)
      (df := fun σ x => ∑ i : ι, DA x (σ i) i *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j)
      (v := v)
      (fun σ _ => (hp σ).1)
      (fun σ _ => (hp σ).2)
  simpa only [Matrix.det_apply'] using hs
