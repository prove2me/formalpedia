-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_original_intrinsic_negative_band_rate_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:23:40.451479+00:00
-- url     : https://prove2.me/submissions/691dc53f-799f-4271-9cae-7502b618c2a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The intrinsic original marked rate agrees with the Levy rate on negative bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) (markRate : Measure ℝ)
    (hMark : ∀ C : Set ℝ, MeasurableSet C → C ⊆ Iic (-ε) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ C) ∂P) = (T : ℝ≥0∞) * markRate C) :
    markRate.restrict (Iic (-ε)) = X.ν.restrict (Iic (-ε)) := by
  have ht0 : (T : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT)
  have htTop : (T : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  ext C hC
  rw [Measure.restrict_apply hC, Measure.restrict_apply hC]
  have hCmeas : MeasurableSet (C ∩ Iic (-ε)) :=
    hC.inter measurableSet_Iic
  have hCsub : C ∩ Iic (-ε) ⊆ Iic (-ε) := inter_subset_right
  have hL := hMark (C ∩ Iic (-ε)) hCmeas hCsub
  have hR :=
    AvramDividend.Classical.avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
      X T (C ∩ Iic (-ε)) hCmeas ε hε hCsub
  have hScaled : markRate (C ∩ Iic (-ε)) * (T : ℝ≥0∞) =
      X.ν (C ∩ Iic (-ε)) * (T : ℝ≥0∞) := by
    calc
      _ = (T : ℝ≥0∞) * markRate (C ∩ Iic (-ε)) := mul_comm _ _
      _ = (T : ℝ≥0∞) * X.ν (C ∩ Iic (-ε)) := hL.symm.trans hR
      _ = X.ν (C ∩ Iic (-ε)) * (T : ℝ≥0∞) := mul_comm _ _
  exact (ENNReal.mul_left_inj ht0 htTop).mp hScaled
