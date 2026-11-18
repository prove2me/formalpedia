-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:01:12.509148+00:00
-- url     : https://prove2.me/submissions/31122a9f-9feb-414f-960f-d658e9ce34aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- The source-faithful upper-strip drift correction sums over physical cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (Δ : ℝ) * max X.c 0 else 0) := by
  dsimp
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ ∧ b <
      x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω ∧
      b < x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω
  · simp only [if_pos h]
    exact avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
      X x b q w D ω n m i h.2.1 h.2.2
  · simp [h]
