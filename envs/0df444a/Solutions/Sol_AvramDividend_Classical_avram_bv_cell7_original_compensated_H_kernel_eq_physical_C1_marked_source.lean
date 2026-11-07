-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_compensated_H_kernel_eq_physical_C1_marked_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:46:11.24337+00:00
-- url     : https://prove2.me/submissions/426d25b2-08a7-4ecf-92ed-0d666116c26c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical-horizon cutoff in the original C1 mark source is redundant
    on the same original stopped-ruin-clock support used by the compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let H : ℝ≥0 × ℝ → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    ∀ p : ℝ≥0 × ℝ,
      H p = Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0) := by
  let r : ℝ≥0∞ := min (ruinTime X x D ω) (T : ℝ≥0∞)
  let τ : ℝ≥0 := r.toNNReal
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let H : ℝ≥0 × ℝ → ℝ := fun p =>
    if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
      (w (Y p.1 + p.2) - w (Y p.1)) else 0
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  have hrfinite : r < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
  have hco : ((τ : ℝ≥0) : ℝ≥0∞) = r :=
    ENNReal.coe_toNNReal (ne_of_lt hrfinite)
  have hτT : τ ≤ T := by
    have hle : (τ : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      rw [hco]
      exact min_le_right _ _
    exact_mod_cast hle
  change ∀ p : ℝ≥0 × ℝ,
    H p = Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
  intro p
  by_cases hp : p ∈ E
  · have htime : p.1 ≤ τ := hp.1
    have hT : p.1 ≤ T := le_trans htime hτT
    simp [H, K, hp, hT]
  · simp [H, hp]
