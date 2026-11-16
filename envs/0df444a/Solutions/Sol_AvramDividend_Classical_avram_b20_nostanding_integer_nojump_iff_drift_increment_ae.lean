-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_nostanding_integer_nojump_iff_drift_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:23:00.605807+00:00
-- url     : https://prove2.me/submissions/dc1a8a5c-267e-4ea4-ae56-ed5aeff3c799

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ (s t : ℕ), s ≤ t →
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s : ℝ≥0) (t : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ↔
        X.X (t : ℝ≥0) ω - X.X (s : ℝ≥0) ω =
          (((t : ℝ≥0) : ℝ) - ((s : ℝ≥0) : ℝ)) * X.drift) := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro t
  let T : ℝ≥0 := (t : ℝ≥0) + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hBound : (t : ℝ≥0) ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_right (by positivity)
  have hNoJump := avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
    X hBV hFinite T hT
  have hMass := avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
    X hBV
  filter_upwards [hNoJump, hMass] with ω hnω hmω
  intro hst
  have hst' : (s : ℝ≥0) ≤ (t : ℝ≥0) := by exact_mod_cast hst
  have hEquiv :=
    avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
      X ω (s : ℝ≥0) (t : ℝ≥0)
  constructor
  · intro hZero
    have hNo := hEquiv.mp hZero
    have hDrift := hnω (s : ℝ≥0) (t : ℝ≥0) hst' hBound hNo
    have hReal := hDrift
    simp only [NNReal.coe_natCast] at hReal
    have hd : X.X (t : ℝ≥0) ω - X.X (s : ℝ≥0) ω =
        ((t : ℝ) - (s : ℝ)) * X.drift := by
      linear_combination -hReal
    simpa only [NNReal.coe_natCast] using hd
  · intro hDrift
    have hSum := hmω (s : ℝ≥0) (t : ℝ≥0) hst'
    have hd : X.X (t : ℝ≥0) ω - X.X (s : ℝ≥0) ω =
        ((t : ℝ) - (s : ℝ)) * X.drift := by
      simpa only [NNReal.coe_natCast] using hDrift
    have hR : ((t : ℝ) * X.drift - X.X (t : ℝ≥0) ω) -
        ((s : ℝ) * X.drift - X.X (s : ℝ≥0) ω) = 0 := by
      linear_combination -hd
    simp only [NNReal.coe_natCast, hR, ENNReal.ofReal_zero] at hSum
    have hSumZero : (∑' u : ℝ≥0,
        if (s : ℝ≥0) < u ∧ u ≤ (t : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) u - X.X u ω) else 0) = 0 :=
      le_antisymm hSum bot_le
    have hEach : ∀ u : ℝ≥0,
        (if (s : ℝ≥0) < u ∧ u ≤ (t : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) u - X.X u ω) else 0) = 0 := by
      exact ENNReal.tsum_eq_zero.mp hSumZero
    apply hEquiv.mpr
    intro u hu
    have hu' : (s : ℝ≥0) < u ∧ u ≤ (t : ℝ≥0) := ⟨hu.1, hu.2⟩
    have he := hEach u
    simp only [if_pos hu'] at he
    have hs0 : (0 : ℝ≥0) ≤ (s : ℝ≥0) := by positivity
    have hNeg := avram_wave4_04a_actual_levy_jumpmark_nonpositive
      X ω u (lt_of_le_of_lt hs0 hu.1)
    have he' := ENNReal.ofReal_eq_zero.mp he
    linarith
