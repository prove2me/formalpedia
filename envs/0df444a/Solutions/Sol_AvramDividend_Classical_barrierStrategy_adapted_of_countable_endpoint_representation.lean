-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_adapted_of_countable_endpoint_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T09:17:56.508982+00:00
-- url     : https://prove2.me/submissions/468a83d5-b491-497a-a060-ef73bceb8c1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (S : Set ℝ≥0) (hS : S.Countable)
    (hrep : ∀ t ω,
      barrierStrategy X c c t ω =
        if t = 0 then 0 else
          max 0 (max
            (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
            (X.X t ω))) :
    Adapted 𝓕 (barrierStrategy X c c) := by
  intro t
  by_cases ht : t = 0
  · subst t
    have heq0 :
        barrierStrategy X c c 0 = (fun _ : Ω => (0 : ℝ)) := by
      funext ω
      simpa using hrep 0 ω
    rw [heq0]
    exact measurable_const
  · have hsup : Measurable[𝓕 t]
        (fun ω => ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω) :=
      (countable_pastSup_adapted X S hS) t
    have hXt : Measurable[𝓕 t] (X.X t) :=
      X.adapted t
    have hmeas : Measurable[𝓕 t]
        (fun ω => max 0
          (max
            (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
            (X.X t ω))) :=
      measurable_const.max (hsup.max hXt)
    have heq :
        barrierStrategy X c c t =
          (fun ω => max 0
            (max
              (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω)
              (X.X t ω))) := by
      funext ω
      simpa [ht] using hrep t ω
    rw [heq]
    exact hmeas
