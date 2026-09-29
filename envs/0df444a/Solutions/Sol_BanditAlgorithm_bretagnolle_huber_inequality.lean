-- Prove2me | solution 1 for BanditAlgorithm.bretagnolle_huber_inequality
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-19T01:22:34.412372+00:00
-- url     : https://prove2.me/submissions/00d5be2f-7c70-453e-a48e-9f7ba2f8451c

import Theorems.Thm_BanditAlgorithm_le_cam_inequality

open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  let ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have h_affinity :
      ∫⁻ ω, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν ≤ P A + Q Aᶜ := by
    calc
      ∫⁻ ω, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν =
          (∫⁻ ω in A, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν) +
            ∫⁻ ω in Aᶜ, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν :=
        (lintegral_add_compl _ hA).symm
      _ ≤ (∫⁻ ω in A, P.rnDeriv ν ω ∂ν) +
            ∫⁻ ω in Aᶜ, Q.rnDeriv ν ω ∂ν := by
        exact add_le_add
          (setLIntegral_mono (Measure.measurable_rnDeriv _ _) fun _ _ ↦ min_le_left _ _)
          (setLIntegral_mono (Measure.measurable_rnDeriv _ _) fun _ _ ↦ min_le_right _ _)
      _ = P A + Q Aᶜ := by
        rw [Measure.setLIntegral_rnDeriv hPν, Measure.setLIntegral_rnDeriv hQν]
  have h_lecam := BanditAlgorithm.le_cam_inequality P Q hD
  have h_enn :
      ENNReal.ofReal (2⁻¹ * exp (-(klDiv P Q).toReal)) ≤
        ENNReal.ofReal (P.real A + Q.real Aᶜ) := by
    rw [ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg)]
    simpa [Measure.real, ν] using h_lecam.trans h_affinity
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_enn
