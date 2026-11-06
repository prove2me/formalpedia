-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_cash_endpoint_discount_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:57:44.342125+00:00
-- url     : https://prove2.me/submissions/2044d6c5-98cf-44d0-aeb6-e3e69910714f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On each actual stopped-grid cash cell, the physical dividend's
discount factor lies between the two endpoint discount factors. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ)
    (t : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    t ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) →
      Real.exp (-(q * (u (i + 1) : ℝ))) ≤
        Real.exp (-(q * t)) ∧
      Real.exp (-(q * t)) ≤
        Real.exp (-(q * (u i : ℝ))) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change t ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) → _
  intro ht
  have hLow : (u i : ℝ) ≤ t := le_of_lt ht.1
  have hHigh : t ≤ (u (i + 1) : ℝ) := ht.2
  have hMulLow := mul_le_mul_of_nonneg_left hLow hq
  have hMulHigh := mul_le_mul_of_nonneg_left hHigh hq
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    linarith
