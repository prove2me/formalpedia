-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:36:02.071309+00:00
-- url     : https://prove2.me/submissions/5e0659e4-a697-4bc9-8365-d58744682802

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_408915f

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
/-- Finite bounded weak factors with compact-local L2 directional derivatives
have the Leibniz weak derivative, including the empty product. -/
theorem solution {n : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, FunctionalInequalities.Analysis.HasWeakDerivAlong (f i) (df i) v)
    (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  revert hf hbound hdf2
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      simp only [Finset.prod_empty, Finset.sum_empty]
      constructor
      · simpa using
          (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_408915f
            (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
            contDiff_const v)
      · intro S _
        exact MemLp.zero
  | @insert i t hi ih =>
      intro hf hbound hdf2
      have hrest := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdf2 j (Finset.mem_insert_of_mem hj))
      have hrest_top :
          MemLp (fun x => ∏ j ∈ t, f j x) (⊤ : ENNReal)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simpa only [ENNReal.inv_top, Finset.sum_const_zero, ENNReal.inv_zero] using
          (MemLp.prod' (p := fun _ : ι => (⊤ : ENNReal))
            (fun j hj => hbound j (Finset.mem_insert_of_mem hj)))
      have hbinary :=
        (hf i (Finset.mem_insert_self i t)).mul_of_locally_memLp_two_408915f
          hrest.1
          (hbound i (Finset.mem_insert_self i t))
          hrest_top
          (hdf2 i (Finset.mem_insert_self i t))
          hrest.2
      have hprod :
          (fun x => ∏ j ∈ insert i t, f j x) =
            (fun x => f i x * ∏ j ∈ t, f j x) := by
        funext x
        exact Finset.prod_insert hi
      have hsum :
          (fun x => ∑ j ∈ insert i t, df j x * ∏ k ∈ (insert i t).erase j, f k x) =
            (fun x => df i x * (∏ j ∈ t, f j x) +
              f i x * ∑ j ∈ t, df j x * ∏ k ∈ t.erase j, f k x) := by
        funext x
        rw [Finset.sum_insert hi, Finset.erase_insert hi, Finset.mul_sum]
        apply congrArg (fun r : ℝ => df i x * (∏ j ∈ t, f j x) + r)
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := by
          intro h
          subst j
          exact hi hj
        have hiErase : i ∉ t.erase j := by
          intro h
          exact hi (Finset.mem_of_mem_erase h)
        rw [Finset.erase_insert_of_ne hij, Finset.prod_insert hiErase]
        exact mul_left_comm _ _ _
      rw [hprod, hsum]
      exact hbinary
