-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_countable_caps_hit_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:08:29.154663+00:00
-- url     : https://prove2.me/submissions/15996f1d-b92f-4dd2-b7be-aaf76304bd19

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_iSup_countable
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (caps : ℕ → ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ,
        WithTop.some (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {caps n}))) :=
  isStoppingTime_iSup_countable _ (fun n =>
    reflectedSup_capped_closedLevelHit_stoppingTime X (caps n) x)
