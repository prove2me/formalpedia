-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_reward_zero_at_instant_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:28:29.701216+00:00
-- url     : https://prove2.me/submissions/add9cba6-2979-424f-9721-fc55a5334e35

import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ω : Ω)
    (hRuin : barrierRuinTime X a ω = 0) :
    (∫⁻ t in paymentTimes (barrierRuinTime X a ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by
  have hPay : paymentTimes (0 : ℝ≥0∞) = ({0} : Set ℝ) := by
    ext t
    change (0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < 0)) ↔ t = 0
    constructor
    · rintro ⟨-, h⟩
      rcases h with h0 | hlt
      · exact h0
      · exact False.elim ((not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal t)) hlt)
    · intro ht
      subst t
      exact ⟨le_refl _, Or.inl rfl⟩
  have hZero :
      (dividendMeasure (runningSup X) ω).restrict ({0} : Set ℝ) = 0 :=
    Measure.restrict_eq_zero.mpr
      (runningSup_dividendMeasure_zero_atom X ω)
  rw [hRuin, hPay]
  change (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t)))
    ∂((dividendMeasure (runningSup X) ω).restrict ({0} : Set ℝ))) = 0
  rw [hZero]
  simp
