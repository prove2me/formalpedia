-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:25:46.884422+00:00
-- url     : https://prove2.me/submissions/a5baf38b-1c89-485c-a862-c3cea616af43

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : WithTop ℝ≥0)) := by
  have hDividend : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuin := ruinTime_stopping_rightCont_filtration X x D hDividend
  have hMin : IsStoppingTime 𝓕.rightCont
      (fun ω => min (ruinTime X x D ω) (T : ℝ≥0∞)) :=
    hRuin.min_const T
  have hFinite (ω : Ω) :
      min (ruinTime X x D ω) (T : ℝ≥0∞) ≠ ⊤ := by
    have hlt : min (ruinTime X x D ω) (T : ℝ≥0∞) < ⊤ :=
      lt_of_le_of_lt (min_le_right _ _) (by simp)
    exact ne_of_lt hlt
  have hEq : (fun ω : Ω =>
      (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : WithTop ℝ≥0)) =
      (fun ω => min (ruinTime X x D ω) (T : ℝ≥0∞)) := by
    funext ω
    exact ENNReal.coe_toNNReal (hFinite ω)
  rw [hEq]
  exact hMin

