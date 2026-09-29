-- Prove2me | solution 1 for FamousTheorems.bounded_continuous_dense_Lp_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:38.780013+00:00
-- url     : https://prove2.me/submissions/a458f5f4-9cf7-4c9b-a67c-dc51c1005437

import Mathlib

theorem solution {α : Type*} [TopologicalSpace α] [NormalSpace α] [MeasurableSpace α] [BorelSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : MeasureTheory.Measure α) [μ.WeaklyRegular]
    {p : ENNReal} [Fact (1 ≤ p)] [SecondCountableTopologyEither α E] (hp : p ≠ ⊤) :
    Dense (MeasureTheory.Lp.boundedContinuousFunction E p μ : Set (MeasureTheory.Lp E p μ)) :=
  MeasureTheory.Lp.boundedContinuousFunction_dense E μ hp
