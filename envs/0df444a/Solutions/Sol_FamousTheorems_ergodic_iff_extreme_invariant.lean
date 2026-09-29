-- Prove2me | solution 1 for FamousTheorems.ergodic_iff_extreme_invariant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:15:36.491914+00:00
-- url     : https://prove2.me/submissions/8c6f842c-03c7-4d6f-8ad0-31667d987861

import Mathlib

open MeasureTheory

theorem solution {X : Type*} {m : MeasurableSpace X} {μ : Measure X} {f : X → X} [IsProbabilityMeasure μ] :
    Ergodic f μ ↔
      μ ∈ Set.extremePoints ENNReal {ν : Measure X | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  Ergodic.iff_mem_extremePoints
