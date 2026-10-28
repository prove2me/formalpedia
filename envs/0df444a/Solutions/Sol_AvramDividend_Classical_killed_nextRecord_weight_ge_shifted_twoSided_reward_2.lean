-- Prove2me | solution 2 for AvramDividend.Classical.killed_nextRecord_weight_ge_shifted_twoSided_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:07:53.163563+00:00
-- url     : https://prove2.me/submissions/5c19e0d2-4759-450f-88a6-e5bec53269aa

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_shifted_twoSided_exit_killed_discount_eq_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual killed next-record weight dominates the discounted
future two-sided exit reward on a surviving first-record path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (r : ℝ≥0)
      (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)))
    (hσ : σ = (⨅ (r : ℝ≥0)
      (_ : X.X (u + r) ω - X.X u ω < ε - a),
      (r : ℝ≥0∞))) :
    ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
          (if ρ < σ then
            ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
          else 0)) ≤
      (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) := by
  by_cases hExit : ρ < σ
  · have hFinite : ρ ≠ ⊤ := ne_top_of_lt hExit
    let T : ℝ≥0 := ρ.toNNReal
    have hT : (T : ℝ≥0∞) = ρ := ENNReal.coe_toNNReal hFinite
    have hUp : (T : ℝ≥0∞) =
        (⨅ (r : ℝ≥0)
          (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)) :=
      hT.trans hρ
    have hDown : (T : ℝ≥0∞) <
        (⨅ (r : ℝ≥0)
          (_ : X.X (u + r) ω - X.X u ω < ε - a),
          (r : ℝ≥0∞)) := by
      rw [hT, ← hσ]
      exact hExit
    have hReward :=
      shifted_twoSided_exit_killed_discount_eq_product
        X a b ε q ha hb hε ω u T hu hAt hBefore hUp hDown
    have hReal : (T : ℝ) = ρ.toReal := by
      rw [← hT, ENNReal.coe_toReal]
    rw [if_pos hExit, ← hReal]
    exact le_of_eq hReward.symm
  · rw [if_neg hExit, mul_zero, mul_zero]
    exact zero_le