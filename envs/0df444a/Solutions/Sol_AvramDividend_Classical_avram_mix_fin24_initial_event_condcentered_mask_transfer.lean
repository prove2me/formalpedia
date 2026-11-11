-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin24_initial_event_condcentered_mask_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:11:13.319426+00:00
-- url     : https://prove2.me/submissions/a666bdba-e349-4ec6-9de8-9217dc67725e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_gfinite32_masked_stopped_integral_le_of_centered_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A centred conditional local certificate bounds any larger initial event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (E T : Set Ω) (hE : MeasurableSet[m] E) (hET : E ⊆ T)
    (b : ℝ) (hb : 0 ≤ b)
    (R M : Ω → ℝ)
    (hRI : Integrable R P) (hMI : Integrable M P)
    (hM0 : P[M | m] =ᵐ[P] 0)
    (hUpper : ∀ᵐ ω ∂(P.restrict E), R ω ≤ b + M ω) :
    (∫ ω in E, R ω ∂P) ≤ b * (P T).toReal := by
  have hZero : (∫ ω in E, M ω ∂P) = 0 :=
    @avram_ubv_jump11_past_event_integral_of_condexp_zero
      Ω mΩ P inferInstance m hm M hMI hM0 E hE
  have hUpperE : (∫ ω in E, R ω ∂P) ≤ (∫ _ω in E, b ∂P) :=
    @avram_gfinite32_masked_stopped_integral_le_of_centered_upper
      Ω mΩ P E b R M hRI.integrableOn hMI.integrableOn
      (integrable_const b).integrableOn hZero hUpper
  have hMeasure : (P E).toReal ≤ (P T).toReal :=
    ENNReal.toReal_mono (measure_ne_top P T) (measure_mono hET)
  calc
    (∫ ω in E, R ω ∂P) ≤ (∫ _ω in E, b ∂P) := hUpperE
    _ = b * (P E).toReal := by simp [integral_const, Measure.real, mul_comm]
    _ ≤ b * (P T).toReal := mul_le_mul_of_nonneg_left hMeasure hb
