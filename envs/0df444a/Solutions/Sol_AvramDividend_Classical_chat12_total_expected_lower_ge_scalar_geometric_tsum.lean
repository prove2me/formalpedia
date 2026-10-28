-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_lower_ge_scalar_geometric_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:47:39.161158+00:00
-- url     : https://prove2.me/submissions/2caf9445-60d3-412b-b71c-a61690115c4b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueExit_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) ≤
      (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) := by
  apply ENNReal.tsum_le_tsum
  intro n
  have hRaw := chat12_firstRecord_geometric_trueExit_lower X q a ε ha hε n
  rw [hExit] at hRaw
  have hterm : ENNReal.ofReal (ε * p ^ (n + 1)) =
      ENNReal.ofReal ε * (ENNReal.ofReal p) ^ (n + 1) := by
    rw [ENNReal.ofReal_mul (le_of_lt hε), ENNReal.ofReal_pow]
    all_goals exact hp
  rw [hterm]
  exact hRaw
