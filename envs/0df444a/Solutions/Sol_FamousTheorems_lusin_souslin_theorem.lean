-- Prove2me | solution 1 for FamousTheorems.lusin_souslin_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:45:36.943403+00:00
-- url     : https://prove2.me/submissions/ced8402d-9284-4716-a1c8-d158a8b55e8f

import Mathlib

theorem solution {γ β : Type*} [TopologicalSpace γ] [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : γ → β} (hf : Continuous f) (hinj : Function.Injective f) :
    MeasurableSet (Set.range f) :=
  MeasureTheory.measurableSet_range_of_continuous_injective hf hinj
