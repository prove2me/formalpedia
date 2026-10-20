-- Prove2me | solution 1 for AvramDividend.Classical.truncated_dividend_payoff_at_zero_eq_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:07:43.60922+00:00
-- url     : https://prove2.me/submissions/93e989b3-2b0e-4fdf-817b-8f91aec941b0

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
  have hset : paymentTimes σ ∩ Iic (0 : ℝ) = {(0 : ℝ)} := by
    ext t
    constructor
    · rintro ⟨ht, ht0⟩
      exact le_antisymm ht0 ht.1
    · intro ht
      have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
      subst t
      refine ⟨⟨le_refl _, Or.inl rfl⟩, ?_⟩
      change (0 : ℝ) ≤ (0 : ℝ)
      exact le_refl _
  have hmass : dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
    simpa using
      (dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0))
  rw [hset, lintegral_singleton]
  simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
    one_mul] using hmass
