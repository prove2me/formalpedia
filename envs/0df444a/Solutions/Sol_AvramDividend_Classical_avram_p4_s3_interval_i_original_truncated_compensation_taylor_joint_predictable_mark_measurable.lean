-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_truncated_compensation_taylor_joint_predictable_mark_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:30:54.366031+00:00
-- url     : https://prove2.me/submissions/e59c25c7-cf8e-49a8-bb09-b747a9952944

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

/-- Jointly predictable genuine original Itô–Meyer Taylor jump kernel
with the correct physical Lévy mark threshold -1 for compensation. -/
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
        (fun y : ℝ => w (y + p.2) - w y -
          (if -1 < p.2 then p.2 * deriv w y else 0))
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) := by
  have hY :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod inferInstance
  have hYm : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hY.measurable
  have hYp : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) :=
    hYm.comp measurable_fst
  have hZp : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => p.2) :=
    measurable_snd
  have hSmall : MeasurableSet
      {p : ((ℝ≥0 × Ω) × ℝ) | -1 < p.2} :=
    hZp measurableSet_Ioi
  have hCorr : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if -1 < p.2 then p.2 *
        deriv w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)
      else (0 : ℝ)) :=
    Measurable.ite hSmall
      (hZp.mul ((measurable_deriv w).comp hYp)) measurable_const
  exact ((hw.comp (hYp.add hZp)).sub (hw.comp hYp)).sub hCorr
