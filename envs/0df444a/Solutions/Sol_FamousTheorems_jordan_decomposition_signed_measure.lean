-- Prove2me | solution 1 for FamousTheorems.jordan_decomposition_signed_measure
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:43:09.815268+00:00
-- url     : https://prove2.me/submissions/cab41bfd-eb42-4927-90ef-8f65e1ab7c37

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] (s : SignedMeasure α) :
    ∃! j : JordanDecomposition α, j.toSignedMeasure = s :=
  ⟨s.toJordanDecomposition, s.toSignedMeasure_toJordanDecomposition,
    fun _ hj => JordanDecomposition.toSignedMeasure_injective (hj.trans s.toSignedMeasure_toJordanDecomposition.symm)⟩
