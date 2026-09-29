-- Prove2me | solution 1 for FamousTheorems.kl_divergence_data_processing
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:11:39.78098+00:00
-- url     : https://prove2.me/submissions/eead3032-933e-4f33-a1c1-2e66474aa647

import Mathlib

open MeasureTheory

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : α → β} (hg : Measurable g) :
    InformationTheory.klDiv (μ.map g) (ν.map g) ≤ InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_map_le μ ν hg
