-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedIncrements_bddAbove_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:20:05.236025+00:00
-- url     : https://prove2.me/submissions/51808df5-ff0b-4a81-80a1-b9e906605d2a

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u T : ℝ≥0) :
    BddAbove
      ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
        Set.Icc 0 T) := by
  obtain ⟨M, hM⟩ := AvramDividend.Classical.levyPath_bddAbove_Icc X ω (u + T)
  refine ⟨M - X.X u ω, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have : X.X (u + r) ω ≤ M := hM ⟨u + r, ⟨zero_le, (add_le_add_iff_left u).2 hr.2⟩, rfl⟩
  simp only
  linarith
