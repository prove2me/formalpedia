-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_terminal_zero_prestate_fixed_negative_mark_raw_value_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:14:02.429453+00:00
-- url     : https://prove2.me/submissions/4a1b7963-dd6f-4d7f-a378-3fa1b0c898df

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (z : ℝ) (hz : z < 0)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ m in atTop, 0 ≤ u m) :
    Tendsto (fun m => w (u m + z) - w (u m))
      atTop (𝓝 (-w 0)) := by
  have hwithin : Tendsto u atTop (𝓝[Ici (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, hpos⟩
  have hw : ContinuousWithinAt w (Ici 0) 0 :=
    hw_cont 0 (by simp)
  have hlimw : Tendsto (fun m => w (u m))
      atTop (𝓝 (w 0)) := by
    simpa only [Function.comp_def] using hw.tendsto.comp hwithin
  have hneg : ∀ᶠ m in atTop, u m + z < 0 := by
    have hlt : ∀ᶠ m in atTop, u m < -z :=
      hu.eventually (Iio_mem_nhds (neg_pos.mpr hz))
    filter_upwards [hlt] with m hm
    linarith
  have heq : (fun m => w (u m + z)) =ᶠ[atTop]
      (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [hneg] with m hm
    exact hw_neg (u m + z) hm
  have hzlim : Tendsto (fun m => w (u m + z))
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 (0 : ℝ))).congr' heq.symm
  simpa only [zero_sub] using hzlim.sub hlimw
