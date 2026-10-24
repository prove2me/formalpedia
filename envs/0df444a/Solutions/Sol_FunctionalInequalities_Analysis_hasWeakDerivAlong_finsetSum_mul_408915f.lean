-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:02:47.407168+00:00
-- url     : https://prove2.me/submissions/0c4eceee-abca-448a-a03b-f14a978bfbd4

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
section WeakFinitePolynomials
open MeasureTheory Set Filter
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
/-- Finite real linear combinations preserve the exact directional weak
derivative and its L2 membership on compact sets. -/
theorem solution {n : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, FunctionalInequalities.Analysis.HasWeakDerivAlong (f i) (df i) v)
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hcf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * f i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).1.smul (c i)
  have hcdf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * df i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).2.1.smul (c i)
  refine ⟨?_, ?_⟩
  · refine ⟨locallyIntegrable_finsetSum s hcf,
      locallyIntegrable_finsetSum s hcdf, ?_⟩
    intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have iF : ∀ i ∈ s,
        Integrable (fun x => (c i * f i x) * fderiv ℝ ψ x v)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcf i hi).integrable_smul_left_of_hasCompactSupport hψd hψdc
    have iG : ∀ i ∈ s,
        Integrable (fun x => (c i * df i x) * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcdf i hi).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    calc
      (∫ x, (∑ i ∈ s, c i * f i x) * fderiv ℝ ψ x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ i ∈ s, ∫ x, (c i * f i x) * fderiv ℝ ψ x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iF
      _ = ∑ i ∈ s, -(∫ x, (c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc, integral_const_mul,
          (hf i hi).2.2 ψ hψ hψc, mul_neg]
      _ = -(∫ x, (∑ i ∈ s, c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        symm
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iG
  · intro S hS
    exact memLp_finsetSum s (fun i hi => (hdf2 i hi S hS).const_mul (c i))
