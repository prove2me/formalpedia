-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:06:40.655688+00:00
-- url     : https://prove2.me/submissions/3f27fba0-4a41-4b5c-8fe6-05f1d4f702cb

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The shifted record contains its zero-time value, making the increment nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) - X.X u ω := by
  let S : Set ℝ := (fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t
  obtain ⟨C, hC⟩ := hb
  have hS : BddAbove S := by
    refine ⟨C, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    apply hC
    exact ⟨u + r, ⟨zero_le, add_le_add_right hr.2 u⟩, rfl⟩
  have hmem : X.X u ω ∈ S := by
    exact ⟨0, by simp, by simp⟩
  have hnonneg : 0 ≤ sSup S - X.X u ω :=
    sub_nonneg.mpr (le_csSup hS hmem)
  rw [barrierStrategy_after_firstUpcrossing_shift X x a hxa u t ω hu
    ⟨C, hC⟩]
  exact max_eq_right hnonneg
