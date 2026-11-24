-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.iSup_min_nat
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T10:58:41.909313+00:00
-- url     : https://prove2.me/submissions/bfbe5ded-b042-4af2-9aed-36bf43d3df92

import Mathlib

open ENNReal

theorem solution (a : ENNReal) : ⨆ n : ℕ, min a n = a := by
  apply le_antisymm
  · exact iSup_le fun n => min_le_left a (n : ENNReal)
  · by_cases ha : a = ⊤
    · simp [ha, iSup_natCast]
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
      conv_lhs => rw [(min_eq_left (le_of_lt hn)).symm]
      exact le_iSup (fun n : ℕ => min a (n : ENNReal)) n
