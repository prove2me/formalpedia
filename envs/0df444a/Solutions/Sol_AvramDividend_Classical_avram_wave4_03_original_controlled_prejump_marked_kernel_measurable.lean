-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:04:43.363607+00:00
-- url     : https://prove2.me/submissions/1684d82b-87ec-40a6-8810-c768f63f3436

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual stopped controlled source may be paired with a Borel jump mark.
    This is only the predictable marked-integrand measurability interface,
    not the original-X Lévy jump compensator or an Itô formula. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
        w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) := by
  have hPre :
      IsStronglyPredictable 𝓕.rightCont
        (fun t ω => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) at hPre
  have hZ : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hPre.measurable
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hZmark : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) :=
    hZ.comp measurable_fst
  exact (hw.comp (hZmark.add measurable_snd)).sub (hw.comp hZmark)
