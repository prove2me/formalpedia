-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:28:49.57726+00:00
-- url     : https://prove2.me/submissions/1c0e7527-2f0d-4029-8710-747177972282

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original discounted stopped C1 marked kernel vanishes
    strictly beyond the smaller of the ruin and physical horizon clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q c a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    ∀ p : ℝ≥0 × ℝ, min T τ < p.1 → F p = 0 := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ E then K p else 0))
  change ∀ p : ℝ≥0 × ℝ, min T τ < p.1 → F p = 0
  intro p hp
  have hNoBoth : ¬(p.1 ≤ T ∧ p.1 ≤ τ) := by
    intro h
    exact (not_le.mpr hp) (le_min h.1 h.2)
  by_cases hpT : p.1 ≤ T
  · have hpτ : ¬p.1 ≤ τ := fun h => hNoBoth ⟨hpT, h⟩
    have hpE : p ∉ E := by
      intro h
      exact hpτ h.1
    simp [F, hpE]
  · simp [F, K, hpT]
