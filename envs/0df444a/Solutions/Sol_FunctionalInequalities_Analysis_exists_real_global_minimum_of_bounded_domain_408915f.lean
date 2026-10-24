-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:21:33.080135+00:00
-- url     : https://prove2.me/submissions/77de34ab-0d96-442e-8c6d-b547394cc79e

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
omit [MeasurableSpace E] [BorelSpace E] in
/-- A proper LSC potential with bounded effective domain attains a finite real
minimum. The real conversion is made only after excluding both infinities. -/
theorem solution
    (φ : E → EReal) (L : NNReal)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hlsc : LowerSemicontinuous φ)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) :
    ∃ a ∈ closedBall (0 : E) (L : ℝ), ∃ m : ℝ,
      φ a = (m : EReal) ∧ ∀ y, (m : EReal) ≤ φ y := by
  classical
  obtain ⟨z, hz⟩ := hfinite
  have hzB : z ∈ closedBall (0 : E) (L : ℝ) := hdom z hz
  obtain ⟨a, haB, haMin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      (show (closedBall (0 : E) (L : ℝ)).Nonempty from ⟨z, hzB⟩)
      (isCompact_closedBall (0 : E) (L : ℝ))
      (hlsc.lowerSemicontinuousOn (closedBall (0 : E) (L : ℝ)))
  change ∀ y ∈ closedBall (0 : E) (L : ℝ), φ a ≤ φ y at haMin
  have haTop : φ a ≠ ⊤ := by
    intro hat
    have h := haMin z hzB
    rw [hat] at h
    exact hz (top_unique h)
  have haReal : ((φ a).toReal : EReal) = φ a :=
    EReal.coe_toReal haTop (hbot a)
  refine ⟨a, haB, (φ a).toReal, haReal.symm, ?_⟩
  intro y
  rw [haReal]
  by_cases hy : φ y = ⊤
  · rw [hy]
    exact le_top
  · exact haMin y (hdom y hy)
