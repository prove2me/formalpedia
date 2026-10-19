-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceFirstBranch_central_radius_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/2902d69f-73f3-4046-8550-7ec8feaac7a6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_saddleSourceFirstBranch_central_radius_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              saddleSourceFirstBranchCentralRadius ε ℓ u < κ := by
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear :=
      (tendsto_id.mono_left
        (nhdsWithin_le_nhds :
          𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hnear] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, heps,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a := by
    intro a ha
    have h := hmargin a ha
    nlinarith
  intro κ hκ
  let A : ℝ := (2 + ε / 2) / Real.sqrt (2 * ε)
  have htendsto :
      Tendsto (fun x : ℝ => A * x ^ (-(5 / 12 : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    convert! tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < 5 / 12)) using 1
    all_goals simp
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (htendsto.eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * N)]
    with ℓ hℓ hlog
  intro u hu huupper hstar
  have hxN : N ≤ ℓ * (1 + u) := by
    nlinarith
  exact (saddleSourceFirstBranch_central_radius_le
    hε hεsmall hℓ hu huupper horder hmargin').trans_lt
      (hN (ℓ * (1 + u)) hxN)
end CohnElkies
