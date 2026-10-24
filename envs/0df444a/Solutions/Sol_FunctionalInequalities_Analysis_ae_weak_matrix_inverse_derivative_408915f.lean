-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:04:55.687414+00:00
-- url     : https://prove2.me/submissions/6da304c5-6936-4824-b8c3-2536861c57b7

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_bounded_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_408915f

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Weak derivatives are unique almost everywhere. -/
theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e
end
end
universe u
end
end

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section WeakMatrixInverse
open MeasureTheory Set Matrix
open scoped ContDiff Topology
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
/-- The given weak derivatives of a locally bounded inverse pair satisfy the
inverse formula almost everywhere; no classical differentiability is assumed. -/
theorem solution {d m : ℕ}
    {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hR : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
    (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => A x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DR x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DR x = -(R x * DA x * R x) := by
  classical
  have hentry (i j : Fin m) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        (DR x * A x + R x * DA x) i j = 0 := by
    have hp (a : Fin m) :=
      (hR i a).mul_of_locally_bounded_408915f (hA a j)
        (hR_top i a) (hA_top a j) (hDR2 i a) (hDA2 a j)
    have hs :=
      FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_408915f
        (Finset.univ : Finset (Fin m)) (fun _ => (1 : ℝ))
        (fun a _ => (hp a).1)
        (fun a _ => (hp a).2)
    have hw :
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun x => (R x * A x) i j)
          (fun x => (DR x * A x + R x * DA x) i j) v := by
      simpa only [one_mul, Matrix.mul_apply, Matrix.add_apply,
        Finset.sum_add_distrib] using hs.1
    have hc :
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          (fun _ => (0 : ℝ)) v := by
      simpa using
        (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_408915f
          (f := fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          contDiff_const v)
    have he :
        (fun x => (R x * A x) i j) =ᵐ[
          (volume : Measure (EuclideanSpace ℝ (Fin d)))]
        (fun _ => (1 : Matrix (Fin m) (Fin m) ℝ) i j) :=
      hRA.mono (fun _ hx => congrArg (fun B => B i j) hx)
    exact (hw.congr_ae_408915f he Filter.EventuallyEq.rfl).ae_eq hc
  have hall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        ∀ i j, (DR x * A x + R x * DA x) i j = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hentry i j))
  filter_upwards [hRA, hall] with x hx hentries
  have hzero : DR x * A x + R x * DA x = 0 := by
    ext i j
    exact hentries i j
  have hAR : A x * R x = 1 := mul_eq_one_comm.mp hx
  apply eq_neg_of_add_eq_zero_left
  calc
    DR x + R x * DA x * R x =
        (DR x * A x + R x * DA x) * R x := by
      rw [add_mul, mul_assoc (DR x) (A x) (R x), hAR, mul_one]
    _ = 0 := by rw [hzero, zero_mul]
