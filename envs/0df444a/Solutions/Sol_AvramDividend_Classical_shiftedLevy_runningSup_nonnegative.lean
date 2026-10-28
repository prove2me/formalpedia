-- Prove2me | solution 1 for AvramDividend.Classical.shiftedLevy_runningSup_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:39:04.183852+00:00
-- url     : https://prove2.me/submissions/93ecf617-e705-4ea3-8c3c-2c2980e7a176

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u t : ℝ≥0) :
    0 ≤ sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
        Set.Icc 0 t) := by
  obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω (u + t)
  have hb : BddAbove ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) := by
    refine ⟨M - X.X u ω, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have : X.X (u + v) ω ≤ M := hM ⟨u + v, ⟨zero_le, add_le_add_right hv.2 u⟩, rfl⟩
    simp only; linarith
  refine le_csSup_of_le hb ⟨0, ⟨le_refl _, zero_le⟩, rfl⟩ ?_
  simp
