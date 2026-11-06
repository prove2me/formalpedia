-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_C1_compact_stopped_jump_increment_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:18:22.988333+00:00
-- url     : https://prove2.me/submissions/9e472d87-408a-4e83-8892-e76995eb4224

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Uniform C1 compact-band Lipschitz bound dominates every eventually in-band original negative jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ) (U : Set ℝ)
    (hw : ContDiffOn ℝ 1 w U) (lo hi : ℝ)
    (hSub : Set.Icc lo hi ⊆ U)
    (S : ℝ≥0) (z : ℕ → ℝ≥0 → ℝ)
    (hBand : ∀ᶠ k in atTop,
      ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ≠ 0 →
        z k t ∈ Set.Icc lo hi ∧
        z k t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ k in atTop,
        ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t) ≠ 0 →
          |w (z k t + (X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)) - w (z k t)| ≤
            L * |(X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)| := by
  obtain ⟨L, hL, hLip⟩ :=
    avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
      w U hw lo hi hSub
  refine ⟨L, hL, ?_⟩
  filter_upwards [hBand] with k hk
  intro t ht
  obtain ⟨hz, hzjump⟩ := hk t ht
  let δ : ℝ := X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
  have hBound := hLip (z k t + δ) hzjump (z k t) hz
  have hδ : z k t + δ - z k t = δ := by ring
  rw [hδ] at hBound
  exact hBound
