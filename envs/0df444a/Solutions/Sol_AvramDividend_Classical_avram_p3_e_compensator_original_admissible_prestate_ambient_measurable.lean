-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:30:24.689265+00:00
-- url     : https://prove2.me/submissions/d5d04018-d23f-4dcf-be9e-41482a5c4dbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original admissible pre-payment reserve is measurable on time × Ω. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) := by
  have hle : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod
        ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hp : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
      from avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
        X x D hD.1.1).measurable
  exact hp.mono hle le_rfl
