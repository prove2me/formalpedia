-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_ae_cofinal_ruin_clock_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:53:28.857795+00:00
-- url     : https://prove2.me/submissions/deb091ef-e4bc-4075-bd79-f6eb1ae2e56a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original min(ruin,n) clock and its cofinal true-path spatial clips
are eventually exactly equal on the full-probability cofinality event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → τk k ω = τ ω := by
  filter_upwards [hSsup] with ω hω
  have hlt : (n : ℝ≥0∞) < (⨆ k : ℕ, S k ω) := by
    rw [hω]
    simp
  obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
  refine ⟨K, ?_⟩
  intro k hk
  have hbound : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ S k ω :=
    (min_le_right _ _).trans ((le_of_lt hK).trans (hSmono ω hk))
  rw [hτk k ω, min_eq_left hbound, hτ ω]
