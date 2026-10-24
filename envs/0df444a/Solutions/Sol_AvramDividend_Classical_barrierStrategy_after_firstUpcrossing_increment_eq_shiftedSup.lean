-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:17:19.987694+00:00
-- url     : https://prove2.me/submissions/6014e9fe-aeee-4459-af23-cd6d5e5897fa

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_at_firstUpcrossing_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_record_increment
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The regulator increment after the first barrier upcrossing is a shifted record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω - barrierStrategy X x a u ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) '' Set.Icc 0 t) := by
  have hbu : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    apply hM
    refine ⟨r, ⟨hr.1, ?_⟩, rfl⟩
    exact hr.2.trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from zero_le))
  have hbshift : BddAbove ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    apply hM
    have hrt : u + r ≤ u + t := by
      calc
        u + r = r + u := add_comm u r
        _ ≤ t + u := add_le_add_left hr.2 u
        _ = u + t := add_comm t u
    exact ⟨u + r, ⟨(show (0 : ℝ≥0) ≤ u + r from zero_le), hrt⟩, rfl⟩
  have hzero := barrierStrategy_at_firstUpcrossing_zero X x a hxa ω u hu hbu
  have hrecord :=
    barrierStrategy_after_firstUpcrossing_record_increment X x a hxa u t ω hu hb
  rw [hzero, sub_zero, hrecord]
  exact (shiftedSup_increment_eq_sup_sub (fun r => X.X r ω) u t hbshift).symm
