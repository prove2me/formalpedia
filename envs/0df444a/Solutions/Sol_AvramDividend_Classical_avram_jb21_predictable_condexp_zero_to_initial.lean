-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb21_predictable_condexp_zero_to_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:07:31.300317+00:00
-- url     : https://prove2.me/submissions/63f55483-3268-4ea9-9c68-87bb223734fe

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gb66_filtered_predictable_multiplier_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Predictable centring transfers from the cell filtration to initial information. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (𝓢0 𝓢 : MeasurableSpace Ω)
    (h01 : 𝓢0 ≤ 𝓢) (hS : 𝓢 ≤ mΩ)
    (H Q : Ω → ℝ)
    (hH : StronglyMeasurable[𝓢] H)
    (hHQ : Integrable (fun ω => H ω * Q ω) P)
    (hQ : Integrable Q P)
    (hQzero : P[Q | 𝓢] =ᵐ[P] (fun _ => (0 : ℝ))) :
    P[(fun ω => H ω * Q ω) | 𝓢0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have hCell :=
    avram_gb66_filtered_predictable_multiplier_condExp_zero
      (mΩ := mΩ) (P := P) 𝓢 H Q hH hHQ hQ hQzero
  have hTower :
      P[P[(fun ω => H ω * Q ω) | 𝓢] | 𝓢0] =ᵐ[P]
        P[(fun ω => H ω * Q ω) | 𝓢0] :=
    condExp_condExp_of_le h01 hS
  have hInner :
      P[P[(fun ω => H ω * Q ω) | 𝓢] | 𝓢0] =ᵐ[P]
        P[(fun _ => (0 : ℝ)) | 𝓢0] :=
    condExp_congr_ae hCell
  exact hTower.symm.trans (hInner.trans (by simp))
