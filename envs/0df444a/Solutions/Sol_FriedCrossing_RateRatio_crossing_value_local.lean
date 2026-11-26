-- Prove2me | solution 1 for FriedCrossing.RateRatio.crossing_value_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:52.224012+00:00
-- url     : https://prove2.me/submissions/0445c255-c3be-4cb6-8172-90bfff0a454f

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_RateRatio_eventually_ne_zero_of_linearArrival
import Theorems.Thm_FriedCrossing_RateRatio_ratio_tendsto


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {z p R : ℝ → ℝ} {a b σ τR : ℝ}
    (hz : LinearArrival z a σ) (hp : LinearArrival p b σ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hoff : ∀ᶠ τ in 𝓝[≠] σ, R τ * z τ / p τ = τR) (hR : ContinuousAt R σ) :
    R σ = τR * (b / a) := by
  have hpz := ratio_tendsto hp hz ha
  have hlim : Tendsto R (𝓝[≠] σ) (𝓝 (τR * (b / a))) := by
    refine (hpz.const_mul τR).congr' ?_
    filter_upwards [hoff, eventually_ne_zero_of_linearArrival hz ha,
      eventually_ne_zero_of_linearArrival hp hb] with τ hτ hzτ hpτ
    rw [← hτ]
    field_simp
  exact tendsto_nhds_unique (hR.tendsto.mono_left nhdsWithin_le_nhds) hlim
end FriedCrossing.RateRatio
