-- Prove2me | solution 1 for FamousTheorems.suslin_theorem_analytic_coanalytic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:45:12.218018+00:00
-- url     : https://prove2.me/submissions/639b18e0-37a2-4640-a14e-8d7be75ffa23

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) :
    MeasurableSet s :=
  hs.measurableSet_of_compl hsc
