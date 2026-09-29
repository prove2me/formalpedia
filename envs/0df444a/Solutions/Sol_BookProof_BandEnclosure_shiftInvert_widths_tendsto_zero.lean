-- Prove2me | solution 1 for BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:41.706314+00:00
-- url     : https://prove2.me/submissions/d705ef8a-6fb2-42ae-a8a5-6e34af48c533

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology
set_option autoImplicit false

theorem solution {lo hi : ℕ → ℝ} {nu gam : ℝ} (hnu : nu ≠ 0)
    (hlo : Tendsto lo atTop (𝓝 nu)) (hhi : Tendsto hi atTop (𝓝 nu)) :
    Tendsto (fun m => ((lo m)⁻¹ - gam) - ((hi m)⁻¹ - gam)) atTop (𝓝 0) := by
  simpa using (hlo.inv₀ hnu).sub (hhi.inv₀ hnu)

#print axioms solution
