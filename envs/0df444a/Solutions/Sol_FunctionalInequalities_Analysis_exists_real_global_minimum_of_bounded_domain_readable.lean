-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:11.65312+00:00
-- url     : https://prove2.me/submissions/01101876-a09c-4211-a60f-a880c2870adc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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
