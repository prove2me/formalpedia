-- Prove2me | solution 2 for AvramDividend.Classical.nnreal_rightContinuous_strict_upper_gap_interval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:17:29.170215+00:00
-- url     : https://prove2.me/submissions/b927fceb-1a31-4509-8d4d-f9ba75aa1237

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical Filter Set Topology
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (u : ℝ≥0) (M : ℝ)
    (hRight : ContinuousWithinAt f (Ici u) u)
    (hGap : f u < M) :
    ∃ v : ℝ≥0, u < v ∧
      ∀ t : ℝ≥0, u ≤ t → t < v → f t < M := by
  have h : ∀ᶠ t in 𝓝[≥] u, f t < M := hRight (Iio_mem_nhds hGap)
  obtain ⟨v, hv, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 h
  exact ⟨v, hv, fun t ht1 ht2 => hsub ⟨ht1, ht2⟩⟩
