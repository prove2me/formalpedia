-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_strict_stopped_cell_cash_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:45:20.844679+00:00
-- url     : https://prove2.me/submissions/37210fdf-bc45-4a77-a3c9-fe19e5c945cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger129_original_strict_cell_cash_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (t ρ : ℝ≥0) (htρ : t < ρ)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) (j i : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun r => min ((r : ℝ≥0) * Δ) t
    (∫⁻ r in Ioc (v i : ℝ) (v (i+1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
        Ioc (v i : ℝ) (v (i+1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal := by
  dsimp
  let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun r => min ((r : ℝ≥0) * Δ) t
  have hlt : v (i+1) < ρ :=
    lt_of_le_of_lt (min_le_right _ _) htρ
  exact avram_gledger129_original_strict_cell_cash_support
    X x D ω q ρ hρruin v i hlt
