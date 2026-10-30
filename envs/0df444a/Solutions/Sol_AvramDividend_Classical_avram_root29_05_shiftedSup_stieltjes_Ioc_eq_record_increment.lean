-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shiftedSup_stieltjes_Ioc_eq_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:29:28.535802+00:00
-- url     : https://prove2.me/submissions/f1078e34-3865-4ecf-aad9-da3c793fee98

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_intervalSup_monotone_of_bddAbove
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The genuine Stieltjes dividend measure of each shifted Lévy future
running supremum pays exactly its real running-record increments on intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (s t : ℝ) :
    (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Ioc s t) =
    ENNReal.ofReal
      (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
          Set.Icc 0 t.toNNReal) -
       sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
          Set.Icc 0 s.toNNReal)) := by
  let f : ℝ≥0 → ℝ := fun v => X.X (u + v) ω - X.X u ω
  let M : ℝ≥0 → ℝ := fun r => sSup (f '' Set.Icc 0 r)
  have hb : ∀ r : ℝ≥0, BddAbove (f '' Set.Icc 0 r) := by
    intro r
    obtain ⟨K, hK⟩ := levyPath_bddAbove_Icc X ω (u + r)
    refine ⟨K - X.X u ω, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have hv' : u + v ∈ Set.Icc (0 : ℝ≥0) (u + r) := by
      exact ⟨bot_le, add_le_add_right hv.2 u⟩
    exact sub_le_sub_right
      (hK (Set.mem_image_of_mem (fun z : ℝ≥0 => X.X z ω) hv')) _
  have hM : Monotone M := intervalSup_monotone_of_bddAbove f hb
  have hc : ∀ r : ℝ≥0, ContinuousWithinAt M (Set.Ici r) r := by
    simpa only [M, f] using shiftedSup_right_continuous_of_levy X ω u
  have hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => M v.toNNReal) r =
        M r.toNNReal :=
    rightLim_comp_toNNReal_of_rightContinuous M hc
  simpa only [M, f] using
    (dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
      (fun r (_ : Ω) => M r) ω s t
      (hM.comp (fun _ _ h => Real.toNNReal_le_toNNReal h)) hr)
