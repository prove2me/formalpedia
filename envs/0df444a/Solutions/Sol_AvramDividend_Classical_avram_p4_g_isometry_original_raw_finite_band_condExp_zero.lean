-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_band_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:33:13.230256+00:00
-- url     : https://prove2.me/submissions/d4f7ebc7-614b-4ef1-bc84-943cc76f47a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_past_event_centred_finite_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Raw source finite-band compensated count has conditional mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (hMeas : Measurable N)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    : P[(fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) | 𝓕 s] =ᵐ[P] 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let r : ℝ≥0∞ := ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  have hCount :
      Integrable (fun ω => (N ω).toReal) P :=
    (avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
      X s t hst ε hε B hB hBand hν N hActual hMeas hRect).1
  have hVInt : Integrable (fun ω => (N ω).toReal - r.toReal) P :=
    hCount.sub (integrable_const r.toReal)
  have hEventZero : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫ ω in A, ((N ω).toReal - r.toReal) ∂P) = 0 := by
    intro A hA
    exact avram_p4_g_isometry_original_raw_past_event_centred_finite_band
      X s t hst ε hε B hB hBand hν N hActual hMeas hRect A hA
  have hz :
      (fun _ : Ω => (0 : ℝ)) =ᵐ[P]
      P[(fun ω => (N ω).toReal - r.toReal) | 𝓕 s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hVInt
    · intro A hA hfin
      exact integrableOn_zero
    · intro A hA hfin
      simpa using (hEventZero A hA).symm
    · exact aestronglyMeasurable_const
  exact hz.symm
