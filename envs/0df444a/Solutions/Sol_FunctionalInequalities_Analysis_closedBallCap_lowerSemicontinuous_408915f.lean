-- Prove2me | solution 1 for FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:25.072979+00:00
-- url     : https://prove2.me/submissions/5793ea25-f828-46e1-af88-b2d2146a8ab7

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The top sublevel is the whole ambient space; every other sublevel is an
intersection with the closed ball. This helper honestly assumes input LSC. -/
theorem solution
 (φ : E → EReal) (L : NNReal)
    (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (FunctionalInequalities.Analysis.closedBallCap φ L) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · subst r
    have hs : FunctionalInequalities.Analysis.closedBallCap φ L ⁻¹' Iic (⊤ : EReal) = (univ : Set E) := by
      ext x
      simp
    rw [hs]
    exact isClosed_univ
  · have hs : FunctionalInequalities.Analysis.closedBallCap φ L ⁻¹' Iic r =
        closedBall (0 : E) (L : ℝ) ∩ (φ ⁻¹' Iic r) := by
      ext x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simp [FunctionalInequalities.Analysis.closedBallCap, hx]
      · have hnr : ¬ (⊤ : EReal) ≤ r := by
          intro h
          exact hr (top_unique h)
        simp [FunctionalInequalities.Analysis.closedBallCap, hx, hnr]
    rw [hs]
    exact isClosed_closedBall.inter
      (lowerSemicontinuous_iff_isClosed_preimage.mp hφ r)
