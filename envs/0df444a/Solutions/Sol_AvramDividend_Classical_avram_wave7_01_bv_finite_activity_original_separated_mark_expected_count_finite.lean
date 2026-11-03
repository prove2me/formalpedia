-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_finite_activity_original_separated_mark_expected_count_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:47:50.624002+00:00
-- url     : https://prove2.me/submissions/910084ab-381c-4e33-8c31-3ec1f03a0b2c



import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original-source finite-activity BV separation gives finite expected jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hP : P Set.univ < ⊤)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) < ⊤ := by
  classical
  have hSubMark : Iic (-ε) ⊆ Iio (0 : ℝ) := by
    intro y hy
    calc
      y ≤ -ε := hy
      _ < 0 := neg_lt_zero.mpr hε
  have hSub :
      Ioc (0 : ℝ≥0) T ×ˢ Iic (-ε) ⊆
        Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ) := by
    rintro ⟨u, y⟩ ⟨hut, hy⟩
    exact ⟨hut, hSubMark hy⟩
  have hBound :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) := by
    apply lintegral_mono
    intro ω
    exact measure_mono hSub
  have hMeas : MeasurableSet[𝓕 (0 : ℝ≥0)] (Set.univ : Set Ω) :=
    MeasurableSet.univ
  have hFull :=
    AvramDividend.Classical.avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
      X hBV hFinite 0 T (show 0 ≤ T from zero_le) Set.univ hMeas
  have hT : (((T - 0 : ℝ≥0) : ℝ≥0∞)) < ⊤ := ENNReal.coe_lt_top
  have hMassTime : P Set.univ * (((T - 0 : ℝ≥0) : ℝ≥0∞)) < ⊤ :=
    ENNReal.mul_lt_top hP hT
  have hFullFinite : P Set.univ * (((T - 0 : ℝ≥0) : ℝ≥0∞)) *
      X.ν (Iio (0 : ℝ)) < ⊤ :=
    ENNReal.mul_lt_top hMassTime hFinite
  have hCountFinite :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) ∂P) < ⊤ := by
    simpa using (hFull.trans_lt hFullFinite)
  exact lt_of_le_of_lt hBound hCountFinite