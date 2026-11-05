-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:21:44.302497+00:00
-- url     : https://prove2.me/submissions/69fee0a4-6b46-4f51-b052-91cd7ec89dee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine bounded original ruin clock has exact strict and inclusive
endpoint semantics, including the zero deterministic horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < (τ ω : ℝ≥0∞) ↔
        (t : ℝ≥0∞) < ruinTime X x D ω ∧ t < T) ∧
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ↔
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ t ≤ T) ∧
    (T = 0 → ∀ ω, τ ω = 0) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  have hCoe (ω : Ω) :
      (τ ω : ℝ≥0∞) =
        min (ruinTime X x D ω) (T : ℝ≥0∞) := by
    dsimp [τ]
    apply ENNReal.coe_toNNReal
    exact ne_of_lt
      ((min_le_right (ruinTime X x D ω) (T : ℝ≥0∞)).trans_lt
        ENNReal.coe_lt_top)
  refine ⟨?_, ?_, ?_⟩
  · intro ω t
    rw [hCoe ω, lt_min_iff]
    simp only [ENNReal.coe_lt_coe]
  · intro ω t
    rw [hCoe ω, le_min_iff]
    simp only [ENNReal.coe_le_coe]
  · intro hT ω
    have hτ0 : (τ ω : ℝ≥0∞) = 0 := by
      rw [hCoe ω, hT]
      simp
    exact ENNReal.coe_injective hτ0
