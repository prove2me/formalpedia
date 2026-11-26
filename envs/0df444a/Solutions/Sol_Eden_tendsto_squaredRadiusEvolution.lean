-- Prove2me | solution 1 for Eden.tendsto_squaredRadiusEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:14.560685+00:00
-- url     : https://prove2.me/submissions/5d71cf2d-eb59-47f8-8ea0-853186415180

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_tendsto_radialDiscriminant

set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : s ≠ 1) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop
      (𝓝 (1 + (s - 1) / |s - 1|)) := by
  have hR := (tendsto_radialDiscriminant s).sqrt
  rw [Real.sqrt_sq_eq_abs] at hR
  have hn : |s - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hs)
  exact tendsto_const_nhds.add (tendsto_const_nhds.div hR hn)
end Eden
