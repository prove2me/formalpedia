-- Prove2me | solution 1 for FriedCrossing.RateRatio.ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:44:29.086001+00:00
-- url     : https://prove2.me/submissions/81c28639-1ba5-458d-a1bb-616d7f2ba609

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_FriedCrossing_RateRatio_eventually_ne_nhdsNE

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {z p : ℝ → ℝ} {a b σ : ℝ} (hz : LinearArrival z a σ)
    (hp : LinearArrival p b σ) (hb : b ≠ 0) :
    Tendsto (fun τ => z τ / p τ) (𝓝[≠] σ) (𝓝 (a / b)) := by
  refine (hz.div hp hb).congr' ((eventually_ne_nhdsNE σ).mono fun τ hτ => ?_)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (sub_ne_zero.mpr hτ)]
end FriedCrossing.RateRatio
