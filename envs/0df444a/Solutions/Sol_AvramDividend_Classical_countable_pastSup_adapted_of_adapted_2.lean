-- Prove2me | solution 2 for AvramDividend.Classical.countable_pastSup_adapted_of_adapted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:13:48.951973+00:00
-- url     : https://prove2.me/submissions/685dfe33-de7e-4e16-95e8-cfb158c5b384

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
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
    (hS.mono (fun s hs => hs.1)).to_subtype
  have hm : Measurable[𝓕 t] (fun ω => ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, u s.1 ω) :=
    Measurable.iSup (fun s => (hu s.1).mono (𝓕.mono s.2.2) le_rfl)
  exact hm
