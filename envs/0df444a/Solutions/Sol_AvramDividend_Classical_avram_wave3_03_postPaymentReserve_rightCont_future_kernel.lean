-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_postPaymentReserve_rightCont_future_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:09:19.467241+00:00
-- url     : https://prove2.me/submissions/4430ddaa-c06b-4fb7-adf9-8fc5b8e8b9f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The original post-payment controlled reserve and the complete future
    Levy path have the exact right-continuous past/future product kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A)
    (f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (x + X.X s ω - rightLimit D s ω,
          fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (x + X.X s ω - rightLimit D s ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by
  obtain ⟨Y, hpath, -, -, -⟩ := levy_rightCont_process X
  have hreserve : Measurable[𝓕.rightCont s]
      (fun ω => x + X.X s ω - rightLimit D s ω) :=
    (postPaymentReserve_cadlag_adapted X x D hD).2.2 s
  have hkernel := avram_root29_01_original_future_kernel_past_test
    Y s (fun ω => x + X.X s ω - rightLimit D s ω)
    hreserve A hA f hf
  simpa only [hpath] using hkernel
