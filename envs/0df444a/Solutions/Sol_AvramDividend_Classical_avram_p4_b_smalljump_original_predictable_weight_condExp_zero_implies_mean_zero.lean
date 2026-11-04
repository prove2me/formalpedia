-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:31:01.041333+00:00
-- url     : https://prove2.me/submissions/0b92c120-143f-4e64-8330-8f50265dd135

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Zero right-continuous conditional expectation implies zero actual-space
mean for an integrable, randomly weighted, original-source finite-band
centred marked-jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (rate : ℝ≥0∞) (H : Ω → ℝ)
    (hInt : Integrable (fun ω =>
      H ω * ((J ω).toReal - rate.toReal)) P)
    (hCenter : P[(fun ω => H ω *
      ((J ω).toReal - rate.toReal)) | 𝓕.rightCont s] =ᵐ[P] 0) :
    (∫ ω, H ω * ((J ω).toReal - rate.toReal) ∂P) = 0 := by
  letI : SigmaFinite (P.trim (𝓕.rightCont.le s)) :=
    avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite 𝓕 s
  have hm : 𝓕.rightCont s ≤ mΩ := (𝓕.rightCont).le s
  calc
    (∫ ω, H ω * ((J ω).toReal - rate.toReal) ∂P) =
        ∫ ω, P[(fun x => H x * ((J x).toReal - rate.toReal)) |
          𝓕.rightCont s] ω ∂P := by
      symm
      exact integral_condExp hm
    _ = (∫ ω, (0 : ℝ) ∂P) := integral_congr_ae hCenter
    _ = 0 := by simp
