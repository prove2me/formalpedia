-- Prove2me | solution 1 for CoopetSourcing.WholesalePrice.lemma_5_gap_limit_sign
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:01:10.253767+00:00
-- url     : https://prove2.me/submissions/b193a52c-45d0-4565-aac3-46aaaf44412c

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

lemma sqrt5134_bounds : (71.65 : ℝ) < Real.sqrt 5134 ∧ Real.sqrt 5134 < 71.66 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- With `k = 153(122 - √5134)` and `A = k²/15625 − 1071`, a positive `x` makes the
expression of (7) positive iff `A x < 1092`. -/
lemma eq7_expr_pos_iff (x : ℝ) (hx : 0 < x) :
    0 < 153 * (Real.sqrt 5134 - 122) * x + 125 * Real.sqrt (21 * x * (51 * x + 52)) ↔
      ((153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071) * x < 1092 := by
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  set k := 153 * (122 - Real.sqrt 5134) with hk
  have hk0 : 0 ≤ k * x / 125 := by apply div_nonneg _ (by norm_num); apply mul_nonneg _ hx.le; linarith
  have e : 153 * (Real.sqrt 5134 - 122) * x + 125 * Real.sqrt (21 * x * (51 * x + 52)) =
      125 * (Real.sqrt (21 * x * (51 * x + 52)) - k * x / 125) := by rw [hk]; ring
  rw [e]
  constructor
  · intro h
    have h' : k * x / 125 < Real.sqrt (21 * x * (51 * x + 52)) := by linarith
    rw [Real.lt_sqrt hk0] at h'
    have : x * ((k ^ 2 / 15625 - 1071) * x - 1092) < 0 := by nlinarith
    have := (mul_neg_iff.mp this)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro h
    have h' : k * x / 125 < Real.sqrt (21 * x * (51 * x + 52)) := by
      rw [Real.lt_sqrt hk0]
      have : x * ((k ^ 2 / 15625 - 1071) * x - 1092) < 0 := mul_neg_of_pos_of_neg hx (by linarith)
      nlinarith
    linarith

lemma eq7_root (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) :
    0 < tbar ∧ ((153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071) * tbar = 1092 := by
  obtain ⟨r1, r2⟩ := sqrt5134_bounds
  unfold Eq7 at h7
  set k := 153 * (122 - Real.sqrt 5134) with hk
  have hs : Real.sqrt (21 * tbar * (51 * tbar + 52)) = k * tbar / 125 := by
    rw [hk]; linarith
  have hpos : 0 < tbar := by
    have h0 := Real.sqrt_nonneg (21 * tbar * (51 * tbar + 52))
    rw [hs] at h0
    have hkpos : 0 < k := by rw [hk]; nlinarith
    rcases lt_or_gt_of_ne htbar with h | h
    · nlinarith
    · exact h
  refine ⟨hpos, ?_⟩
  have hX : 0 ≤ 21 * tbar * (51 * tbar + 52) := by positivity
  have := Real.sq_sqrt hX
  rw [hs] at this
  have : tbar * ((k ^ 2 / 15625 - 1071) * tbar - 1092) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h htbar
  · linarith

end CSAux

theorem solution (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : CoopetSourcing.WholesalePrice.Eq7 tbar)
    (t : ℝ) (ht : 35 / 92 < t) (ht7 : t < 7 / 10) :
    ∃ L : ℝ,
      Filter.Tendsto (fun wA : ℝ => CoopetSourcing.WholesalePrice.wSepPool t wA -
          CoopetSourcing.WholesalePrice.wEqualBar t wA)
        (nhdsWithin (1 / 2 - 5 * t / 7) (Set.Iio (1 / 2 - 5 * t / 7))) (nhds L) ∧
      (0 < L ↔ t < tbar) := by
  have htp : 0 < t := by linarith
  refine ⟨wSepPool t (1 / 2 - 5 * t / 7) - wEqualBar t (1 / 2 - 5 * t / 7),
    ((CSAux.gap_cont t).tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
  rw [CSAux.gap_top t htp]
  obtain ⟨hb0, hb⟩ := CSAux.eq7_root tbar htbar h7
  obtain ⟨r1, r2⟩ := CSAux.sqrt5134_bounds
  have hA : 0 < (153 * (122 - Real.sqrt 5134)) ^ 2 / 15625 - 1071 := by nlinarith
  rw [div_pos_iff_of_pos_right (by norm_num), CSAux.eq7_expr_pos_iff t htp]
  constructor
  · intro h; by_contra h'; rw [not_lt] at h'; nlinarith
  · intro h; nlinarith
