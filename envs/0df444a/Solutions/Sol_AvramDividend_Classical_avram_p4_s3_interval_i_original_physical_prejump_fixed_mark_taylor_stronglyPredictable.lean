-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:06:11.680396+00:00
-- url     : https://prove2.me/submissions/240b90e3-daea-4919-af08-64ecdd1c76cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original state-dependent nonlinear fixed-mark Itô–Meyer Taylor kernel
is strongly predictable for the same physical right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (z : ℝ) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        w (y + z) - w y - z * deriv w y) := by
  have hY :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      w (y + z) - w y - z * deriv w y)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hYm : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hY.measurable
  have hWm : Measurable (fun p : ℝ≥0 × Ω =>
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z)) :=
    hw.comp (hYm.add measurable_const)
  have hDm : Measurable (fun p : ℝ≥0 × Ω =>
      deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) :=
    (measurable_deriv w).comp hYm
  exact ((hWm.sub (hw.comp hYm)).sub
    (measurable_const.mul hDm)).stronglyMeasurable
