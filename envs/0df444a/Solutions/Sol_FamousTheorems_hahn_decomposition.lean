-- Prove2me | solution 1 for FamousTheorems.hahn_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:11:21.790436+00:00
-- url     : https://prove2.me/submissions/bbdfadf1-2be8-477f-a4ae-a22409cbf069

import Mathlib

theorem solution {α : Type*} [MeasurableSpace α] (s : MeasureTheory.SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ MeasureTheory.VectorMeasure.restrict 0 i ≤ MeasureTheory.VectorMeasure.restrict s i ∧
      MeasurableSet j ∧ MeasureTheory.VectorMeasure.restrict s j ≤ MeasureTheory.VectorMeasure.restrict 0 j ∧ IsCompl i j :=
  s.exists_isCompl_positive_negative
