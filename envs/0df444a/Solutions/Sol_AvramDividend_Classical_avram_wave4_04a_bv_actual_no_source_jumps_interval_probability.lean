-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_no_source_jumps_interval_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:06:39.327823+00:00
-- url     : https://prove2.me/submissions/6e4ae092-42c2-49a0-82b3-3ff9e75c989b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original BV Lévy jump count has its Poisson zero-jump law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by
  classical
  have hT : 0 < t + 1 := by positivity
  have htT : t ≤ t + 1 :=
    le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1)
  have hAE :
      {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =ᵐ[P]
      {ω : Ω |
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) = 0} := by
    filter_upwards
      [avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
          X hBV hFinite (t + 1) hT,
        bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hNoJumpInterval hmono
    let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
    have hm : Monotone Y := hmono
    apply propext
    change (∀ u : ℝ≥0, u ∈ Ioc s t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) ↔
      Y t - Y s = 0
    constructor
    · intro hNoJump
      have heq : Y t = Y s :=
        hNoJumpInterval s t hst htT hNoJump
      exact sub_eq_zero.mpr heq
    · intro hzero u hu
      have heq : Y t = Y s := sub_eq_zero.mp hzero
      by_contra hnonzero
      have huPos : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hu.1
      have hjump : Function.leftLim Y u < Y u := by
        exact
          (avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
            X ω u huPos).mpr hnonzero
      have hsleft : Y s ≤ Function.leftLim Y u := hm.le_leftLim hu.1
      have hut : Y u ≤ Y t := hm hu.2
      have hstrict : Y s < Y t :=
        lt_of_lt_of_le (lt_of_le_of_lt hsleft hjump) hut
      exact (ne_of_lt hstrict) heq.symm
  have hEq :
      P.real {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =
      P.real {ω : Ω |
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) = 0} := by
    change (P {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0}).toReal =
      (P {ω : Ω |
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) = 0}).toReal
    rw [measure_congr hAE]
  exact hEq.trans
    (bv_actual_residual_increment_zero_probability X hBV hFinite s t hst)
