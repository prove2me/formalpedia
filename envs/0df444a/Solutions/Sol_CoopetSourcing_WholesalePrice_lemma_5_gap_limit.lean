-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_5_gap_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:59:20.204994+00:00
-- url     : https://prove2.me/submissions/c7085399-4994-46f5-ab08-2ef92e90d70f

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

open CoopetSourcing.WholesalePrice

namespace CSAux

lemma gap_cont (t : ℝ) : Continuous (fun wA : ℝ => wSepPool t wA - wEqualBar t wA) := by
  unfold wSepPool wEqualBar profitPool wIBar
  simp only [stateProfitVI, poolQO2H, poolQI, poolQO1]
  fun_prop

lemma gap_top (t : ℝ) (ht : 0 < t) :
    wSepPool t (1 / 2 - 5 * t / 7) - wEqualBar t (1 / 2 - 5 * t / 7) =
      (153 * (Real.sqrt 5134 - 122) * t + 125 * Real.sqrt (21 * t * (51 * t + 52))) / 5250 := by
  have h1 : Real.sqrt (6 * (25 * (1 - 2 * (1 / 2 - 5 * t / 7)) ^ 2 + 6064 * t ^ 2
      - 320 * t * (1 - 2 * (1 / 2 - 5 * t / 7)))) = 18 * Real.sqrt 5134 * t / 7 := by
    have hnn : 0 ≤ 18 * Real.sqrt 5134 * t / 7 := by positivity
    rw [← Real.sqrt_sq hnn]; congr 1
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5134 by norm_num)
    linear_combination (-(324 : ℝ) * t ^ 2 / 49) * this
  have hX : 0 ≤ 21 * t * (51 * t + 52) := by positivity
  have h2 : Real.sqrt ((1 + t) ^ 2 - 32 / 3 * (profitPool t (1 / 2 - 5 * t / 7)
      (wIBar t (1 / 2 - 5 * t / 7)) - ((1 + t) ^ 2 + (1 - t + 2 * (1 / 2 - 5 * t / 7)) ^ 2) / 32))
      = Real.sqrt (21 * t * (51 * t + 52)) / 21 := by
    have hnn : 0 ≤ Real.sqrt (21 * t * (51 * t + 52)) / 21 := by positivity
    rw [← Real.sqrt_sq hnn]; congr 1
    have := Real.sq_sqrt hX
    simp only [profitPool, stateProfitVI, poolQO1, poolQO2H, poolQI, wIBar]
    linear_combination (-(1 : ℝ) / 441) * this
  unfold wSepPool wEqualBar
  rw [h1, h2]
  ring

end CSAux

theorem solution (t : ℝ) (ht : 35 / 92 < t) (ht7 : t < 7 / 10) :
    Filter.Tendsto (fun wA : ℝ => CoopetSourcing.WholesalePrice.wSepPool t wA -
        CoopetSourcing.WholesalePrice.wEqualBar t wA)
      (nhdsWithin (1 / 2 - 5 * t / 7) (Set.Iio (1 / 2 - 5 * t / 7)))
      (nhds ((153 * (Real.sqrt 5134 - 122) * t + 125 * Real.sqrt (21 * t * (51 * t + 52))) / 5250)) := by
  rw [← CSAux.gap_top t (by linarith)]
  exact ((CSAux.gap_cont t).tendsto _).mono_left nhdsWithin_le_nhds
