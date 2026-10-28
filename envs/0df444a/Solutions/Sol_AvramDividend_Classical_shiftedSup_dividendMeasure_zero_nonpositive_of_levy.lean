-- Prove2me | solution 1 for AvramDividend.Classical.shiftedSup_dividendMeasure_zero_nonpositive_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:51:51.867647+00:00
-- url     : https://prove2.me/submissions/f21f7b32-3b8a-4dea-bd68-097afc7c4ed7

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_intervalSup_monotone_of_bddAbove
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0 := by
  classical
  let f : ℝ≥0 → ℝ := fun v => X.X (u + v) ω - X.X u ω
  let M : ℝ≥0 → ℝ := fun r => sSup (f '' Set.Icc 0 r)
  have hb : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t) := by
    intro t
    rcases levyPath_bddAbove_Icc X ω (u + t) with ⟨K, hK⟩
    refine ⟨K - X.X u ω, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have hv' : u + v ∈ Set.Icc (0 : ℝ≥0) (u + t) := by
      exact ⟨bot_le, add_le_add_right hv.2 u⟩
    have hbound : X.X (u + v) ω ≤ K :=
      hK (Set.mem_image_of_mem (fun s : ℝ≥0 => X.X s ω) hv')
    exact sub_le_sub_right hbound _
  have hM : Monotone M :=
    intervalSup_monotone_of_bddAbove f hb
  have hc : ∀ t : ℝ≥0, ContinuousWithinAt M (Set.Ici t) t := by
    simpa only [M, f] using shiftedSup_right_continuous_of_levy X ω u
  have hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => M v.toNNReal) r =
        M r.toNNReal :=
    rightLim_comp_toNNReal_of_rightContinuous M hc
  exact dividendMeasure_Iic_zero_of_monotone_rightLim
    (fun t (_ : Ω) => M t) ω
    (hM.comp (fun _ _ h => Real.toNNReal_le_toNNReal h)) hr