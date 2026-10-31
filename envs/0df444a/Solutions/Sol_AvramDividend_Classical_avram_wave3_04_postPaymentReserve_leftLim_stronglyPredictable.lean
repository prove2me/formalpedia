-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:04:50.111835+00:00
-- url     : https://prove2.me/submissions/e9cc42af-f6c6-4810-b35e-85210f21be92

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine controlled reserve left-limit integrand is strongly
predictable under the transported original right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  let Z : ℝ≥0 → Ω → ℝ :=
    fun s ω => x + X.X s ω - rightLimit D s ω
  have hA : StronglyAdapted 𝓕.rightCont Z :=
    avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont X x D hD
  have hL : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => Z s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    obtain ⟨l, hl, _⟩ :=
      avram_wave3_04_postPaymentReserve_prejump_upper X x D hD ω t ht
    exact ⟨l, hl⟩
  have hStrong : StronglyAdapted 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s => Z s ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits Z hA hL
  have hCont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun u => Function.leftLim (fun s => Z s ω) u) (Iic t) t := by
    intro ω t
    exact avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
      (fun s => Z s ω) (hL ω) t
  exact avram_wave3_04_strongAdapted_leftContinuous_predictable hStrong hCont
