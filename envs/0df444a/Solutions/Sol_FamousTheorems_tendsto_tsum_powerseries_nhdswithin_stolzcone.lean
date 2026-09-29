-- Prove2me | solution 1 for FamousTheorems.tendsto_tsum_powerseries_nhdswithin_stolzcone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:19.955953+00:00
-- url     : https://prove2.me/submissions/b39842eb-602a-467d-bfe2-10ce22d53525

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {f : ℕ → ℂ} {l : ℂ}, 
    Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l) → 
    ∀ {s : ℝ}, 0 < s → Tendsto (fun z => ∑' (n : ℕ), f n * z ^ n) (𝓝[Complex.stolzCone s] 1) (𝓝 l) :=
  @_root_.Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone
