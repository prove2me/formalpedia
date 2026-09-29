-- Prove2me | solution 1 for FamousTheorems.lusin_separation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:43:21.890874+00:00
-- url     : https://prove2.me/submissions/11a13789-5c7c-41cd-a2f9-833c0c85c83b

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {s t : Set α}
    (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) :
    MeasurablySeparable s t :=
  hs.measurablySeparable ht h
