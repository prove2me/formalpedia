-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_expected_full_discounted_stieltjes_reward_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:15:52.549254+00:00
-- url     : https://prove2.me/submissions/98c82208-fd87-414e-bd79-798d0d3c3ea0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

/-- The complete pathwise reward bound integrates over arbitrary original
stopping clocks, retaining every diffuse and chronological payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ ω) ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω : Ω, ENNReal.ofReal (rightLimit D T ω) ∂P) := by
  apply lintegral_mono
  intro ω
  exact avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
    D hD ω T (τ ω) q hq
