-- Prove2me | solution 1 for FamousTheorems.haar_measure_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:32:41.505649+00:00
-- url     : https://prove2.me/submissions/e86436ab-21c5-43e5-8306-8e6b610b455a

import Mathlib

open MeasureTheory

theorem solution {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (μ' μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant] :
    ∃ c : NNReal, μ' = c • μ :=
  ⟨_, MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ' μ⟩
