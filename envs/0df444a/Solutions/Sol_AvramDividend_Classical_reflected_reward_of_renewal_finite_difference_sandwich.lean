-- Prove2me | solution 1 for AvramDividend.Classical.reflected_reward_of_renewal_finite_difference_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:32:02.721461+00:00
-- url     : https://prove2.me/submissions/be37dedd-2f5a-4d7a-afa8-d3801c2f4c77

import Theorems.Thm_AvramDividend_Classical_renewal_scale_finite_difference_limits_of_hasDerivAt
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (V : ℝ≥0∞)
    (hLo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal
        (ε * W (a - ε) / (W a - W (a - ε))) ≤ V)
    (hHi : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      V ≤ ENNReal.ofReal
        (ε * W (a + ε) / (W (a + ε) - W a))) :
    V = ENNReal.ofReal (W a / d) := by
  obtain ⟨hLower, hUpper⟩ :=
    AvramDividend.Classical.renewal_scale_finite_difference_limits_of_hasDerivAt
      W a d hD hd
  have hValue : Tendsto (fun _ : ℝ => V)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hLower hUpper hLo hHi
  exact tendsto_nhds_unique tendsto_const_nhds hValue
