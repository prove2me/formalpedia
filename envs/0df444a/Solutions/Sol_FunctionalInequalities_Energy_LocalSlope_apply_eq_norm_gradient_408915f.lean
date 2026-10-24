-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:15.969521+00:00
-- url     : https://prove2.me/submissions/b7bda719-dbfc-4db2-9cfa-c18983cee95e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities.Energy.LocalSlope in
/-- Step 1: the one-moving-point local slope equals the derivative norm at a differentiable
point, expressed through the canonical Hilbert gradient. No nontriviality premise is needed. -/
theorem solution
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    FunctionalInequalities.Energy.LocalSlope.apply f x = ENNReal.ofReal ‖gradient f x‖ := by
  rw [FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.norm_gradient_eq_norm_fderiv]
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff_ball.mp
      (hf.hasFDerivAt.isLittleO.bound hεr)
    calc
      FunctionalInequalities.Energy.LocalSlope.apply f x ≤ ENNReal.ofReal (‖fderiv ℝ f x‖ + ε) := by
        unfold FunctionalInequalities.Energy.LocalSlope.apply
        refine iInf_le_of_le r (iInf_le_of_le hr ?_)
        refine iSup_le fun y => iSup_le fun hy => ?_
        apply ENNReal.ofReal_le_ofReal
        by_cases hyx : y = x
        · subst y
          simp only [dist_self, div_zero]
          positivity
        · apply (div_le_iff₀ (dist_pos.mpr hyx)).2
          rw [dist_eq_norm, dist_eq_norm]
          calc
            ‖f y - f x‖ = ‖(f y - f x - (fderiv ℝ f x) (y - x)) +
                (fderiv ℝ f x) (y - x)‖ := by rw [sub_add_cancel]
            _ ≤ ‖f y - f x - (fderiv ℝ f x) (y - x)‖ +
                ‖(fderiv ℝ f x) (y - x)‖ := norm_add_le _ _
            _ ≤ ε * ‖y - x‖ + ‖fderiv ℝ f x‖ * ‖y - x‖ :=
              add_le_add (hrem y hy) ((fderiv ℝ f x).le_opNorm _)
            _ = (‖fderiv ℝ f x‖ + ε) * ‖y - x‖ := by ring
      _ = ENNReal.ofReal ‖fderiv ℝ f x‖ + ε := by
        have hadd (a : ℝ) (ha : 0 ≤ a) :
            ENNReal.ofReal (a + (ε : ℝ)) = ENNReal.ofReal a + (ε : ENNReal) := by
          convert! ENNReal.ofReal_add ha ε.2 using 1
          simp
        exact hadd _ (by positivity)
  · unfold FunctionalInequalities.Energy.LocalSlope.apply
    refine le_iInf fun r => le_iInf fun hr => ?_
    let S : ENNReal := ⨆ (y : E) (_ : dist y x < r),
      ENNReal.ofReal (dist (f y) (f x) / dist y x)
    change ENNReal.ofReal ‖fderiv ℝ f x‖ ≤ S
    by_cases hS : S = ⊤
    · simp [hS]
    apply (ENNReal.ofReal_le_iff_le_toReal hS).2
    apply hf.hasFDerivAt.le_of_lip' ENNReal.toReal_nonneg
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    by_cases hyx : y = x
    · subst y
      simp
    · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ S :=
        le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      have := (ENNReal.ofReal_le_iff_le_toReal hS).1 hq
      have := (div_le_iff₀ (dist_pos.mpr hyx)).1 this
      simpa only [dist_eq_norm] using this
