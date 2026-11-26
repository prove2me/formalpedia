-- Prove2me | solution 1 for Eden.tendsto_log_add_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:41.296706+00:00
-- url     : https://prove2.me/submissions/3f16cf4d-4769-4927-b6fa-b08c70148ada

import Definitions.Def_Eden_RealTimeAverages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Eden_LogarithmicSums
import Theorems.Thm_Eden_log_add_bounds

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {f g : ℝ → ℝ} {a b : ℝ}
    (hfpos : ∀ᶠ t in atTop, 0 < f t) (hgpos : ∀ᶠ t in atTop, 0 < g t)
    (hf : Tendsto (fun t => Real.log (f t) / t) atTop (𝓝 a))
    (hg : Tendsto (fun t => Real.log (g t) / t) atTop (𝓝 b)) :
    Tendsto (fun t => Real.log (f t + g t) / t) atTop (𝓝 (max a b)) := by
  have hm := hf.max hg
  have hc : Tendsto (fun t : ℝ => Real.log 2 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm (by simpa using hc.add hm)
  · filter_upwards [hfpos, hgpos, eventually_gt_atTop (0 : ℝ)] with t hft hgt ht
    have h := (div_le_div_of_nonneg_right (log_add_bounds hft hgt).1 ht.le)
    simpa only [max_div_div_right ht.le] using h
  · filter_upwards [hfpos, hgpos, eventually_gt_atTop (0 : ℝ)] with t hft hgt ht
    have h := (div_le_div_of_nonneg_right (log_add_bounds hft hgt).2 ht.le)
    simpa only [add_div, max_div_div_right ht.le] using h
end Eden
