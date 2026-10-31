-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_zero_extended_log_continuous_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:30:06.020385+00:00
-- url     : https://prove2.me/submissions/0dabefa9-1f4e-4ff9-a4da-c648f313f9c5

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set
open scoped Topology ENNReal NNReal

/-- A positive-height ENNReal factor converging to one admits a real
logarithm whose zero extension is continuous at height zero. -/
theorem solution
    (F : ℝ → ℝ≥0∞)
    (hone : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞))) :
    ContinuousAt (fun h : ℝ =>
      if 0 < h then Real.log ((F h).toReal) else 0) 0 := by
  let g : ℝ → ℝ := fun h =>
    if 0 < h then Real.log ((F h).toReal) else 0
  have hR : Tendsto (fun h : ℝ => (F h).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt ENNReal.toReal (1 : ℝ≥0∞) :=
      ENNReal.continuousAt_toReal (by simp)
    simpa only [Function.comp_def, ENNReal.toReal_one] using
      hc.tendsto.comp hone
  have hlog : Tendsto (fun h : ℝ => Real.log ((F h).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num)
    simpa only [Function.comp_def, Real.log_one] using
      hc.tendsto.comp hR
  have hleft : ContinuousWithinAt g (Iio (0 : ℝ)) 0 := by
    have hmem : ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ),
        h ∈ Iio (0 : ℝ) := self_mem_nhdsWithin
    have heq : g =ᶠ[𝓝[<] (0 : ℝ)] (fun _ : ℝ => 0) := by
      filter_upwards [hmem] with h hh
      have hnot : ¬ 0 < h := not_lt.mpr hh.le
      simp only [g, if_neg hnot]
    change Tendsto g (𝓝[<] (0 : ℝ)) (𝓝 (g 0))
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0]
    have hc : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝[<] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds
    exact hc.congr' heq.symm
  have hright : ContinuousWithinAt g (Ioi (0 : ℝ)) 0 := by
    have hmem : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
        h ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    have heq : g =ᶠ[𝓝[>] (0 : ℝ)]
        (fun h : ℝ => Real.log ((F h).toReal)) := by
      filter_upwards [hmem] with h hh
      have hh' : 0 < h := hh
      change (if 0 < h then Real.log ((F h).toReal) else 0) =
        Real.log ((F h).toReal)
      exact if_pos hh'
    change Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0))
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0]
    exact hlog.congr' heq.symm
  exact (continuousAt_iff_continuous_left'_right').2 ⟨hleft, hright⟩
