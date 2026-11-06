-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_contact_cell_cash_le_shrinking_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:41:06.324198+00:00
-- url     : https://prove2.me/submissions/15e740a2-0f37-482b-9e57-0a2df91fcc86

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (T : ℝ≥0) (m i : ℕ) (hi : i < m + 1) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    u (i + 1) = τ →
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  change u (i + 1) = τ → _
  intro hCross
  have hCell : u (i + 1) - u i ≤ T / (m + 1) := by
    simpa only [u, τ] using
      (avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
        X x D T m i hi ω)
  have hDiff : τ - u i ≤ T / (m + 1) := by
    simpa only [hCross] using hCell
  have hUpper : τ ≤ u i + T / (m + 1) := by
    have hUpper' : τ ≤ T / (m + 1) + u i :=
      (tsub_le_iff_right).mp hDiff
    simpa only [add_comm] using hUpper'
  have hFloor : τ - T / (m + 1) ≤ u i :=
    (tsub_le_iff_right).mpr (by simpa only [add_comm] using hUpper)
  have hFloorReal : ((τ - T / (m + 1) : ℝ≥0) : ℝ) ≤ (u i : ℝ) := by
    exact_mod_cast hFloor
  have hIncl :
      paymentTimes (ruinTime X x D ω) ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ) := by
    intro t ht
    rcases ht with ⟨htPay, htInt⟩
    exact ⟨htPay, ⟨lt_of_le_of_lt hFloorReal htInt.1,
      by simpa only [hCross] using htInt.2⟩⟩
  exact lintegral_mono_set hIncl
