-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:27:41.685233+00:00
-- url     : https://prove2.me/submissions/21c638b1-f28b-45fe-b258-3d7fe3ac9f67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The real-valued centred count of an actual finite original Lévy mark
band has zero conditional expectation once its exact ENNReal right-continuous
eventwise intensity is known. All moment assumptions stay explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
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
    (hJmeas : Measurable J)
    (hJfinite : ∀ᵐ ω ∂P, J ω < ⊤)
    (hJint : Integrable (fun ω => (J ω).toReal) P)
    (rate : ℝ≥0∞)
    (hRate : ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont s] A →
      (∫⁻ ω in A, J ω ∂P) = P A * rate) :
    P[(fun ω => (J ω).toReal - rate.toReal) | 𝓕.rightCont s] =ᵐ[P] 0 := by
  have hVint : Integrable (fun ω => (J ω).toReal - rate.toReal) P :=
    hJint.sub (integrable_const rate.toReal)
  apply avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero
    X s (fun ω => (J ω).toReal - rate.toReal) hVint
  intro A hA
  have hRestrictedFinite : ∀ᵐ ω ∂P.restrict A, J ω < ⊤ :=
    ae_restrict_of_ae hJfinite
  have hIntegralReal :
      (∫ ω in A, (J ω).toReal ∂P) =
        (∫⁻ ω in A, J ω ∂P).toReal :=
    integral_toReal hJmeas.aemeasurable hRestrictedFinite
  calc
    (∫ ω in A, (J ω).toReal - rate.toReal ∂P) =
        (∫ ω in A, (J ω).toReal ∂P) - (P A).toReal * rate.toReal := by
      rw [integral_sub hJint.integrableOn (integrableOn_const)]
      simp [integral_const, measureReal_def]
    _ = (P A * rate).toReal - (P A).toReal * rate.toReal := by
      rw [hIntegralReal, hRate A hA]
    _ = 0 := by rw [ENNReal.toReal_mul]; ring
