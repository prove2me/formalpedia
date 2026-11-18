-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB38_barrier_reserve_above_cutoff_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:00:45.486716+00:00
-- url     : https://prove2.me/submissions/b3596d09-7a0e-44de-b686-3dad7db9bd36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- A narrow path tube keeps the original cap-reflected reserve above b. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω)
  (hTube : ∀ s : ℝ≥0, s ≤ t →
    |X.X s ω| ≤ (1 / 400 : ℝ)) :
  (5 / 44 : ℝ) <
    riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω := by
  classical
  have hSup : (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤
      (1 / 400 : ℝ) := by
    letI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
    refine ciSup_le fun s => ?_
    exact (abs_le.mp (hTube s.1 s.2.2)).2
  have hDividend :
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) t ω ≤
        (1 / 400 : ℝ) := by
    unfold barrierStrategy
    split_ifs with h0
    · norm_num
    · have hz : (1 / 8 : ℝ) - 1 / 8 = 0 := by ring
      simp only [hz, zero_add]
      exact max_le (by norm_num) hSup
  have hXt : -(1 / 400 : ℝ) ≤ X.X t ω :=
    (abs_le.mp (hTube t le_rfl)).1
  change (5 / 44 : ℝ) <
    (1 / 8 : ℝ) + X.X t ω -
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) t ω
  linarith
