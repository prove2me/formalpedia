-- Prove2me | solution 1 for Eden.tendsto_squaredRadiusEvolution_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:48.503917+00:00
-- url     : https://prove2.me/submissions/548a54d1-6a80-45f7-9877-047794ee56da

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
theorem _root_.solution {s : ℝ} (hs : s < 1) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 0) := by
  have h := tendsto_squaredRadiusEvolution (ne_of_lt hs)
  have hn : s - 1 ≠ 0 := by linarith
  rw [abs_of_neg (show s - 1 < 0 by linarith), div_neg, div_self hn] at h
  norm_num at h
  exact h
end Eden
