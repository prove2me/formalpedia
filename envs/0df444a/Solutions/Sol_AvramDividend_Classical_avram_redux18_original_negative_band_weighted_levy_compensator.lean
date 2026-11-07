-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_original_negative_band_weighted_levy_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:29:47.051885+00:00
-- url     : https://prove2.me/submissions/0b824584-f903-460d-83cd-f637ed8a461a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Genuine original-process weighted negative-band Campbell compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (ε : ℝ) (hε : 0 < ε)
    (hSupport : ∀ y, y ∉ Iic (-ε) → g y = 0) :
    (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (T : ℝ≥0∞) * (∫⁻ y, g y ∂X.ν) := by
  obtain ⟨markRate, hCounts, hWeighted⟩ :=
    AvramDividend.Classical.avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
      X T g hg
  by_cases hT : T = 0
  · subst T
    simpa using hWeighted
  · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
    have ht0 : (T : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (ne_of_gt hTpos)
    have htTop : (T : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    let B : Set ℝ := Iic (-ε)
    have hB : MeasurableSet B := measurableSet_Iic
    have hRestr : markRate.restrict B = X.ν.restrict B := by
      ext C hC
      rw [Measure.restrict_apply hC, Measure.restrict_apply hC]
      have hCB : MeasurableSet (C ∩ B) := hC.inter hB
      have hSub : C ∩ B ⊆ Iic (-ε) := inter_subset_right
      have hL := hCounts (C ∩ B) hCB
      have hR :=
        AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
          X T (C ∩ B) hCB ε hε hSub
      have hScaled : markRate (C ∩ B) * (T : ℝ≥0∞) =
          X.ν (C ∩ B) * (T : ℝ≥0∞) := by
        calc
          _ = (T : ℝ≥0∞) * markRate (C ∩ B) := mul_comm _ _
          _ = (T : ℝ≥0∞) * X.ν (C ∩ B) := hL.symm.trans hR
          _ = X.ν (C ∩ B) * (T : ℝ≥0∞) := mul_comm _ _
      exact (ENNReal.mul_left_inj ht0 htTop).mp hScaled
    have hLocal (μ : Measure ℝ) :
        (∫⁻ y, g y ∂μ) = ∫⁻ y in B, g y ∂μ := by
      have hIndicator : B.indicator g = g := by
        funext y
        by_cases hy : y ∈ B
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, hSupport y hy, B]
      have hi := MeasureTheory.lintegral_indicator (μ := μ) hB g
      rw [hIndicator] at hi
      exact hi
    have hWeightRate : (∫⁻ y, g y ∂markRate) =
        ∫⁻ y, g y ∂X.ν := by
      calc
        _ = ∫⁻ y in B, g y ∂markRate := hLocal markRate
        _ = ∫⁻ y in B, g y ∂X.ν := by rw [hRestr]
        _ = _ := (hLocal X.ν).symm
    rw [hWeightRate] at hWeighted
    exact hWeighted
