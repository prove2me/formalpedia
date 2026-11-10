-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess17_actual_stopped_zero_contact_count_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:19:48.898425+00:00
-- url     : https://prove2.me/submissions/659cb654-0cf6-483b-be3e-6aa4594fb295

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_original_zero_prestate_source_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (v : ℝ) :
    let J : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
       (Ioc s t ×ˢ Iio (0 : ℝ))
    P[(fun ω => (if (s : ℝ≥0∞) < ruinTime X x D ω ∧
        Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s = 0
      then v else 0) *
      ((J ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  classical
  let A : Set Ω := {ω | (s : ℝ≥0∞) < ruinTime X x D ω ∧
    Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s = 0}
  have hZero :=
    avram_bv_excess17_original_zero_prestate_source_measurable X x D hD s
  have hStop := ruinTime_stopping_rightCont_filtration X x D hD
  have hSurvive : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | (s : ℝ≥0∞) < ruinTime X x D ω} := by
    have hLe : MeasurableSet[𝓕.rightCont s]
        {ω : Ω | ruinTime X x D ω ≤ (s : ℝ≥0∞)} := hStop s
    have hEq : {ω : Ω | (s : ℝ≥0∞) < ruinTime X x D ω} =
        {ω : Ω | ¬ ruinTime X x D ω ≤ (s : ℝ≥0∞)} := by
      ext ω
      simp [not_le]
    rw [hEq]
    exact hLe.compl
  have hA : MeasurableSet[𝓕.rightCont s] A := hSurvive.inter hZero
  have hMeas : StronglyMeasurable[𝓕.rightCont s]
      (fun ω : Ω => if ω ∈ A then v else 0) :=
    (measurable_const.ite hA measurable_const).stronglyMeasurable
  have hBound : ∀ᵐ ω ∂P, ‖(if ω ∈ A then v else 0 : ℝ)‖ ≤ ‖v‖ := by
    filter_upwards [] with ω
    split_ifs <;> simp
  dsimp only
  simpa only [A, Set.mem_setOf_eq] using
    (avram_ubv_jump11_original_finite_band_bounded_predictable_condexp_zero
      X s t hst r hsr hrt hShort hLong (Iio (0 : ℝ)) measurableSet_Iio
      hFinite _ (fun _ => rfl) (fun ω => if ω ∈ A then v else 0) ‖v‖
      hMeas hBound)
