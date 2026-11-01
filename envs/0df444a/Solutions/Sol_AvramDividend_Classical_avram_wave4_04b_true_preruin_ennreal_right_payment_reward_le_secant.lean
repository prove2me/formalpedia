-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_true_preruin_ennreal_right_payment_reward_le_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:45:54.084809+00:00
-- url     : https://prove2.me/submissions/177838f7-7151-48c4-b9cf-008c5c4613cd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section
/-- The full actual discounted pre-ruin right-payment mass is bounded by
its chronological HJump secants as an ENNReal sum, without a summability or
finite secant-growth condition. The time-zero atom is included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (A : Set ℝ)
    (hA : A = {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∑' s : A, ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        (rightLimit D ((s : ℝ).toNNReal) ω -
          D ((s : ℝ).toNNReal) ω))) ≤
    (∑' s : A, ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        (w (riskProcess X x D ((s : ℝ).toNNReal) ω) -
          w (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω -
              D ((s : ℝ).toNNReal) ω))))) := by
  apply ENNReal.tsum_le_tsum
  intro s
  have hMem : (s : ℝ) ∈
      {u : ℝ | u ∈ paymentTimes (ruinTime X x D ω) ∧
        u ≤ (T : ℝ) ∧ 0 < rightLimit D u.toNNReal ω - D u.toNNReal ω} := by
    rw [← hA]
    exact s.property
  have hPay :
      (s : ℝ).toNNReal = 0 ∨
        (((s : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω := by
    have hp := hMem.1
    change (s : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {u : ℝ | ENNReal.ofReal u < ruinTime X x D ω}) at hp
    rcases hp.2 with hzero | hlt
    · left
      have hz : (s : ℝ) = 0 := hzero
      simp [hz]
    · right
      change (((s : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) <
        ruinTime X x D ω at hlt
      exact hlt
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (hjump ((s : ℝ).toNNReal) hPay) (le_of_lt (Real.exp_pos _))
