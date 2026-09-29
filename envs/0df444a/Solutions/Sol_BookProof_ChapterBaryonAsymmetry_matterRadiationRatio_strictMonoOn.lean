-- Prove2me | solution 1 for BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:22:57.320583+00:00
-- url     : https://prove2.me/submissions/15fe43dc-7445-4b14-b28b-e75ad0e0343f

-- Generated from ChapterBaryonAsymmetry.lean — solution of BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
import Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matterRadiationRatio_eq
open BookProof.ChapterBaryonAsymmetry













open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (ρm0 ρr0 : ℝ) (hm : 0 < ρm0) (hr : 0 < ρr0) :
    StrictMonoOn (fun a => matterRadiationRatio ρm0 ρr0 a) (Set.Ioi (0 : ℝ)) := by

  have hk : 0 < ρm0 / ρr0 := div_pos hm hr
  intro x hx y hy hxy
  dsimp only
  rw [matterRadiationRatio_eq _ _ _ hx (ne_of_gt hr),
    matterRadiationRatio_eq _ _ _ hy (ne_of_gt hr)]
  exact mul_lt_mul_of_pos_left hxy hk
