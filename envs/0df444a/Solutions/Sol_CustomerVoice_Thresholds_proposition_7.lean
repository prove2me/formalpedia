-- Prove2me | solution 1 for CustomerVoice.Thresholds.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:11:33.374573+00:00
-- url     : https://prove2.me/submissions/aa88bad5-52b8-4c02-b44b-aebdab174052

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting
import Theorems.Thm_CustomerVoice_Thresholds_Delta_gt_Lambda_iff

open CustomerVoice.Thresholds

theorem solution (M : Model) (hM : M.Standing) :
    M.Delta > M.Lambda ↔
      M.γ < max (2 * M.s / (2 * M.s + M.k))
        ((Real.sqrt (M.s ^ 2 + 4 * M.s * M.k) - M.s) / (2 * M.k)) := by
  obtain ⟨_, _, _, _, hg0, hg1, hk, hs⟩ := hM
  rw [Delta_gt_Lambda_iff M ⟨by assumption, by assumption, by assumption, by assumption,
    hg0, hg1, hk, hs⟩]
  have h1g : 0 < 1 - M.γ := by linarith
  -- ΔL > ΛH1 ↔ γ < 2s/(2s+k)
  have hA : M.DeltaL > M.LambdaH1 ↔ M.γ < 2 * M.s / (2 * M.s + M.k) := by
    unfold Model.DeltaL Model.LambdaH1
    rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) (by positivity),
      lt_div_iff₀ (by positivity)]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have hf : (2 * M.s - (2 * M.s + M.k) * M.γ) * (M.s + M.k * M.γ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      nlinarith
    · intro h
      have hf : 0 < (2 * M.s - (2 * M.s + M.k) * M.γ) * (M.s + M.k * M.γ) :=
        mul_pos (by linarith) (by positivity)
      nlinarith
  -- ΔL > ΛH2 ↔ γ < (√(s²+4sk) − s)/(2k)
  have hB : M.DeltaL > M.LambdaH2 ↔
      M.γ < (Real.sqrt (M.s ^ 2 + 4 * M.s * M.k) - M.s) / (2 * M.k) := by
    unfold Model.DeltaL Model.LambdaH2
    rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) (by positivity),
      lt_div_iff₀ (by positivity), lt_sub_iff_add_lt,
      Real.lt_sqrt (by positivity)]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [gt_iff_lt, min_lt_iff, lt_max_iff, ← gt_iff_lt, ← gt_iff_lt, hA, hB]
