-- Prove2me | solution 1 for FamousTheorems.steinhaus
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:21:08.101417+00:00
-- url     : https://prove2.me/submissions/7f7ac723-c23b-49c5-8fad-2cebc057293f

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [LocallyCompactSpace G] [μ.InnerRegular] (E : Set G)
    (hE : MeasurableSet E) (hEpos : 0 < μ E) : E / E ∈ nhds (1 : G) :=
  MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos μ E hE hEpos
