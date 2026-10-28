-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_eq_densePrefix_onSample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:36:55.302412+00:00
-- url     : https://prove2.me/submissions/772d736b-3136-40b2-8513-9d1f4a5e4ff1

import Mathlib.Topology.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_with_endpoint
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At a scheduled endpoint, dense observations alone recover the entire running maximum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (ht : t ∈ S) (ω : Ω) :
    runningSup X t ω =
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω := by
  have hmain := runningSup_eq_densePrefix_with_endpoint X S hDense h0 t ω
  have hb : BddAbove
      (Set.range (fun s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t} => X.X s.1 ω)) := by
    obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω t
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩, rfl⟩
  have hterminal :
      X.X t ω ≤ (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω) :=
    le_ciSup hb ⟨t, ht, le_rfl⟩
  simpa [max_eq_left hterminal] using hmain
