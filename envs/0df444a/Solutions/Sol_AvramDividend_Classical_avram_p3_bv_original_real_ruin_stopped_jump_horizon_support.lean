-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_real_ruin_stopped_jump_horizon_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:57:37.723194+00:00
-- url     : https://prove2.me/submissions/f5449035-ce36-43f4-bfd1-39b665a38341

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine controlled real-horizon ruin clock never exceeds ruin, and
every stopped original-jump integrand is supported on its physical horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      S.indicator H = H := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
  have hBound : ∀ ω, τ ω ≤ T :=
    (avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
      X x D hD T).1
  have hτeq (ω : Ω) : (τ ω : ℝ≥0∞) =
      min (ruinTime X x D ω) (T : ℝ≥0∞) := by
    dsimp [τ]
    apply ENNReal.coe_toNNReal
    have hT : (T : ℝ≥0∞) < ⊤ := by simp
    exact ne_top_of_lt (lt_of_le_of_lt
      (min_le_right (ruinTime X x D ω) (T : ℝ≥0∞)) hT)
  constructor
  · intro ω
    rw [hτeq]
    exact min_le_left _ _
  · funext p
    by_cases hp : p ∈ S
    · have hpt : p.1.1 ≤ T := hp
      simp [Set.indicator, S, hpt]
    · have hnot : ¬ p.1.1 ≤ T := hp
      have hstop : ¬ ((p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞)) := by
        intro hle
        apply hnot
        have hle' : p.1.1 ≤ τ p.1.2 := by exact_mod_cast hle
        exact le_trans hle' (hBound p.1.2)
      simp [Set.indicator, S, H, hnot, hstop]
