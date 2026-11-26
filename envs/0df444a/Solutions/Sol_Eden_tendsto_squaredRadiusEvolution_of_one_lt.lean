-- Prove2me | solution 1 for Eden.tendsto_squaredRadiusEvolution_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:56.614693+00:00
-- url     : https://prove2.me/submissions/82e7ce95-1dcd-4d16-bd98-42a168144938

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_tendsto_squaredRadiusEvolution

set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 2) := by
  have h := tendsto_squaredRadiusEvolution (ne_of_gt hs)
  have hn : s - 1 ≠ 0 := by linarith
  rw [abs_of_pos (show 0 < s - 1 by linarith), div_self hn] at h
  norm_num at h
  exact h
end Eden
