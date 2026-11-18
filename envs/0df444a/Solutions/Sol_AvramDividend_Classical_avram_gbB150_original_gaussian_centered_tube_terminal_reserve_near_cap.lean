-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:11:13.223723+00:00
-- url     : https://prove2.me/submissions/7c4a830f-0971-4b2a-bc9a-a59041cf251b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Quantitative original reflected terminal reserve under centred Gaussian tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ T →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ T →
      |B s| ≤ (1 / 4000 : ℝ)) :
    (1 / 8 : ℝ) - (1 / 2000 : ℝ) ≤
      riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω := by
  classical
  have hSup :
      (⨆ s : Icc (0 : ℝ≥0) T, X.X s ω) ≤
        2 * (T : ℝ) + (1 / 4000 : ℝ) := by
    letI : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
    refine ciSup_le fun s => ?_
    have hs := hSource s.1 s.2.2
    have hB := (abs_le.mp (hCentered s.1 s.2.2)).2
    have hTime : (s.1 : ℝ) ≤ (T : ℝ) := s.2.2
    linarith
  have hD :
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) T ω ≤
        2 * (T : ℝ) + (1 / 4000 : ℝ) := by
    unfold barrierStrategy
    rw [if_neg (ne_of_gt hT)]
    have hzero : (1 / 8 : ℝ) - 1 / 8 = 0 := by ring
    simp only [hzero, zero_add]
    exact max_le (by positivity) hSup
  have hX : 2 * (T : ℝ) - (1 / 4000 : ℝ) ≤
      X.X T ω := by
    have ht := hSource T le_rfl
    have hB := (abs_le.mp (hCentered T le_rfl)).1
    linarith
  change (1 / 8 : ℝ) - (1 / 2000 : ℝ) ≤
    (1 / 8 : ℝ) + X.X T ω -
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) T ω
  linarith
