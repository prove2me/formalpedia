-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_source_slack_ratio_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:48:19.853191+00:00
-- url     : https://prove2.me/submissions/a54968a8-5a3b-44c3-a6ec-2f304740e749

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal
open scoped Topology
noncomputable section

/-- The deterministic correction for nonzero initial value converges to one. -/
theorem solution
    (w : ℝ) (hw : 0 < w) (e : ℕ → ℝ)
    (he : Filter.Tendsto e Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => ENNReal.ofReal (w / (w + e n)))
      Filter.atTop (nhds (1 : ℝ≥0∞)) := by
  have hden : Tendsto (fun n => w + e n) atTop (𝓝 w) := by
    simpa using (tendsto_const_nhds.add he)
  have hnum : Tendsto (fun _ : ℕ => w) atTop (𝓝 w) := tendsto_const_nhds
  have hratio0 : Tendsto (fun n => w / (w + e n))
      atTop (𝓝 (w / w)) :=
    hnum.div hden (ne_of_gt hw)
  have hratio : Tendsto (fun n => w / (w + e n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa [div_self (ne_of_gt hw)] using hratio0
  have hENN := (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hratio
  change Tendsto (fun n => ENNReal.ofReal (w / (w + e n)))
    atTop (𝓝 (ENNReal.ofReal (1 : ℝ))) at hENN
  simpa using hENN
