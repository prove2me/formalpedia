-- Prove2me | solution 1 for CostlyShort.OneAsset.prop3_eq31_from_eq29
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:51:32.491164+00:00
-- url     : https://prove2.me/submissions/89646ce8-ed2b-45ca-9b16-34b047b7bebc

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting
open CostlyShort.OneAsset

theorem solution(σ δ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ ^ 2 < s * δ) :
    costOne σ δ s = ((δ + yieldOne σ δ s) * s - σ ^ 2) / (1 + s) := by
  have h1 : (1:ℝ) - s ≠ 0 := by linarith
  have h2 : (1:ℝ) + s ≠ 0 := by linarith
  have h3 : s ≠ 0 := hs0.ne'
  unfold costOne yieldOne
  rw [if_pos hreg, if_pos hreg]
  field_simp
  ring
