-- Prove2me | solution 1 for FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:44.620561+00:00
-- url     : https://prove2.me/submissions/9ee6fcd6-1261-4e97-97df-55eddf1885e4

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section Separation
variable {X : Type*} [MetricSpace X]
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities.Energy in
/-- Finitely many pairwise disjoint compact sets have one common thickening radius keeping the
thickenings pairwise disjoint. -/
theorem solution (N : ℕ) (Kc : ℕ → Set X)
    (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨ρ₁, hρ₁, hsep₁⟩ := ih
    set U : Set X := ⋃ i : Fin N, Kc (i : ℕ) with hU
    have hUcompact : IsCompact U := isCompact_iUnion fun i ↦ hcomp _
    have hdisjU : Disjoint (Kc N) U := by
      rw [hU, Set.disjoint_iUnion_right]
      intro i
      exact hdisj N i (by omega)
    obtain ⟨ρ₂, hρ₂, hsep₂⟩ := hdisjU.exists_thickenings (hcomp N) hUcompact.isClosed
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun i hi j hj hij ↦ ?_⟩
    have hsubU : ∀ k, k < N → Metric.thickening (min ρ₁ ρ₂) (Kc k) ⊆ Metric.thickening ρ₂ U := by
      intro k hk
      refine subset_trans (Metric.thickening_mono (min_le_right _ _) _) ?_
      exact Metric.thickening_subset_of_subset _ (Set.subset_iUnion (fun i : Fin N ↦ Kc i) ⟨k, hk⟩)
    have hsubN : Metric.thickening (min ρ₁ ρ₂) (Kc N) ⊆ Metric.thickening ρ₂ (Kc N) :=
      Metric.thickening_mono (min_le_right _ _) _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono (Metric.thickening_mono (min_le_left _ _) _)
          (Metric.thickening_mono (min_le_left _ _) _) (hsep₁ i hi' j hj' hij)
      · subst hj'
        exact Disjoint.mono (hsubU i hi') hsubN hsep₂.symm
    · subst hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono hsubN (hsubU j hj') hsep₂
      · exact absurd hj'.symm hij
