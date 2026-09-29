-- Prove2me | solution 3 for BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:27:45.457709+00:00
-- url     : https://prove2.me/submissions/6ac65407-8607-41c5-8558-8f75272410c0

-- Generated from ChapterBaryonAsymmetry.lean — solution of BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
import Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matterRadiationRatio_eq
open BookProof.ChapterBaryonAsymmetry













open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (ρm0 ρr0 : ℝ) (hm : 0 < ρm0) (hr : 0 < ρr0) :
    Tendsto (fun a => matterRadiationRatio ρm0 ρr0 a) atTop atTop := by

  have hk : 0 < ρm0 / ρr0 := div_pos hm hr
  have heq : (fun a => matterRadiationRatio ρm0 ρr0 a) =ᶠ[atTop] (fun a => (ρm0 / ρr0) * a) := by
    filter_upwards [eventually_gt_atTop 0] with a ha
    exact matterRadiationRatio_eq _ _ _ ha (ne_of_gt hr)
  rw [tendsto_congr' heq]
  exact Filter.Tendsto.const_mul_atTop hk tendsto_id
