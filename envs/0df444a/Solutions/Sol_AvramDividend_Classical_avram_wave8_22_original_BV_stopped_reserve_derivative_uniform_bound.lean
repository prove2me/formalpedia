-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_stopped_reserve_derivative_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:28:49.06806+00:00
-- url     : https://prove2.me/submissions/0e89f831-989f-4a74-ba61-72a8dc288c8e

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- On the genuine stopped controlled reserve, the original BV compact-cap C¹ regularity yields one deterministic derivative ceiling. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (C : ℝ≥0∞) (w : ℝ → ℝ)
  (hwC1 : ContDiffOn ℝ 1 w
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (a b : ℝ) (hab : a ≤ b)
  (hBand : Icc a b ⊆
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (A : Ω → Set ℝ≥0)
  (Y : (ℝ≥0 × Ω) → ℝ)
  (hY : ∀ p, Y p = Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
  (hStoppedBand : ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 → Y p ∈ Icc a b) :
  ∃ L : ℝ, 0 ≤ L ∧
    ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 → |deriv w (Y p)| ≤ L := by
  obtain ⟨L, hL, hBound⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
      X hBV C w hwC1 a b hab hBand
  exact ⟨L, hL, fun p hp => hBound (Y p) (hStoppedBand p hp)⟩
