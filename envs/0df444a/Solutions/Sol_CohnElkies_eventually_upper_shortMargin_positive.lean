-- Prove2me | solution 1 for CohnElkies.eventually_upper_shortMargin_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/c4c4c455-f18b-45e5-a00a-385fef4f0175

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_upper_one_add_shortEndpoint_scaled

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε),
        (1 / 2 : ℝ) ≤ shortMargin ε a := by
  have hscaled :
      Tendsto (fun ε : ℝ =>
        10 * (ε * (1 + shortEndpoint ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert! tendsto_upper_one_add_shortEndpoint_scaled.const_mul
      (10 : ℝ) using 1; norm_num
  have hsmall := hscaled.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall]
    with ε hε hbound a ha
  change 0 < ε at hε
  unfold shortMargin
  have hcompare :
      ε * (1 + a) ≤ ε * (1 + shortEndpoint ε) :=
    mul_le_mul_of_nonneg_left (by linarith [ha.2]) hε.le
  change 10 * (ε * (1 + shortEndpoint ε)) < 1 / 2
    at hbound
  nlinarith
end CohnElkies
