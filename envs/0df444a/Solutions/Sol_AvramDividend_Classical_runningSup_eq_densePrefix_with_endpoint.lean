-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_eq_densePrefix_with_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:28:02.793971+00:00
-- url     : https://prove2.me/submissions/92b94721-77b9-4ea7-a265-71a98298f3b7

import Mathlib.Topology.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The true regulator at a finite time is recovered by dense path samples and the endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (ω : Ω) :
    runningSup X t ω =
      max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
        (X.X t ω) := by
  rw [(runningSup_eq_rawSup_nonneg X t ω).1]
  apply dense_timeSup_with_endpoint _ (X.rightCont ω) S hDense h0 t
  obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω t
  refine ⟨M, ?_⟩
  rintro y ⟨s, rfl⟩
  exact hM ⟨s.1, s.2, rfl⟩
