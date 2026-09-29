-- Prove2me | solution 1 for FamousTheorems.haar_measure_exists_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:49:19.042382+00:00
-- url     : https://prove2.me/submissions/e2b6cbe2-eb8d-491e-b817-14d09cad4d51

import Mathlib

theorem solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : ∃ μ : MeasureTheory.Measure G, μ.IsHaarMeasure :=
  ⟨_, MeasureTheory.Measure.isHaarMeasure_haarMeasure (Classical.arbitrary _)⟩
