-- Prove2me | solution 1 for AvramDividend.Classical.levy_exp_clock_survival_null_fixed_horizon_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:33:46.851704+00:00
-- url     : https://prove2.me/submissions/ee869159-1c09-4c23-850f-7510d65aa4b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p T : ℝ) (hp : 0 < p)
    (hClockPos : 0 < (expMeasure p) (Iic T))
    (hClockNull :
      (P.prod (expMeasure p))
        {z : Ω × ℝ | ∀ s : ℝ≥0,
          s ≤ z.2.toNNReal → 0 ≤ X.X s z.1} = 0) :
    P {ω : Ω | ∀ s : ℝ≥0,
      s ≤ T.toNNReal → 0 ≤ X.X s ω} = 0 := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  let A : Set Ω := {ω | ∀ s : ℝ≥0,
    s ≤ T.toNNReal → 0 ≤ X.X s ω}
  let B : Set (Ω × ℝ) := {z | ∀ s : ℝ≥0,
    s ≤ z.2.toNNReal → 0 ≤ X.X s z.1}
  have hSubset : A ×ˢ (Iic T) ⊆ B := by
    intro z hz
    rcases hz with ⟨hzA, hzT⟩
    intro s hs
    exact hzA s (le_trans hs (Real.toNNReal_mono hzT))
  have hZero : (P.prod (expMeasure p)) (A ×ˢ Iic T) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      (P.prod (expMeasure p)) (A ×ˢ Iic T) ≤
          (P.prod (expMeasure p)) B := measure_mono hSubset
      _ = 0 := hClockNull
  have hMul : P A * (expMeasure p) (Iic T) = 0 := by
    simpa only [Measure.prod_prod] using hZero
  exact (mul_eq_zero.mp hMul).resolve_right (ne_of_gt hClockPos)
