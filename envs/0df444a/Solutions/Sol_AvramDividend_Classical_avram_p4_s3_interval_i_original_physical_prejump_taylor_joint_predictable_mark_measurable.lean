-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:20:38.448082+00:00
-- url     : https://prove2.me/submissions/94caed7b-1a2d-4866-b477-c1cb8fc48723

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

/-- Jointly measurable nonlinear Taylor kernel in the actual physical
predictable time-path sigma algebra times the original Lévy mark space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        (fun y : ℝ => w (y + p.2) - w y - p.2 * deriv w y)
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 -
              rightLimit D s p.1.2) p.1.1)) := by
  have hY :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod inferInstance
  have hYm : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hY.measurable
  have hYp : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) :=
    hYm.comp measurable_fst
  have hZp : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => p.2) :=
    measurable_snd
  exact ((hw.comp (hYp.add hZp)).sub (hw.comp hYp)).sub
    (hZp.mul ((measurable_deriv w).comp hYp))
