-- Prove2me | solution 1 for AvramDividend.Classical.countable_pastSup_adapted_of_adapted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:12:49.295295+00:00
-- url     : https://prove2.me/submissions/412770e3-0f04-4cb7-9cfd-bc1417f14c15

import Mathlib

open MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (S : Set ℝ≥0) (hS : S.Countable) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, u s.1 ω) := by
  intro t
  have : Countable {s : ℝ≥0 // s ∈ S ∧ s ≤ t} :=
    (hS.mono (fun s (hs : s ∈ S ∧ s ≤ t) => hs.1)).to_subtype
  have hm : Measurable[𝓕 t] (fun ω => ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, u s.1 ω) :=
    Measurable.iSup fun s => (hu s.1).mono (𝓕.mono s.2.2) le_rfl
  exact hm
