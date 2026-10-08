-- Prove2me | solution 1 for AvramDividend.Classical.countable_pastSup_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:30:41.545567+00:00
-- url     : https://prove2.me/submissions/282cd0ee-cf03-461b-aec6-6d6d2e9c0904

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω) := by
  intro t
  have hst : ({s : ℝ≥0 | s ∈ S ∧ s ≤ t}).Countable := by
    exact hS.mono (by intro s hs; exact hs.1)
  letI : Countable {s : ℝ≥0 // s ∈ S ∧ s ≤ t} := hst.to_subtype
  apply Measurable.iSup
  intro s
  exact X.adapted.measurable_le s.2.2
