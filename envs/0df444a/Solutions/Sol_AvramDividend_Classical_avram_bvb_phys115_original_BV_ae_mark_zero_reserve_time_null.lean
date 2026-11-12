-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys115_original_BV_ae_mark_zero_reserve_time_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:59:35.045538+00:00
-- url     : https://prove2.me/submissions/e6f76432-ff8b-44ba-b7ce-4525c72ccea0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Almost every original BV negative mark cancels the reserve only
on a time-null set, the Fubini-ready phys95 boundary exclusion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (μ : Measure ℝ≥0) [SFinite μ]
    (U : ℝ≥0 → ℝ) (hU : Measurable U) :
    ∀ᵐ z ∂X.ν, μ {t : ℝ≥0 | U t = -z} = 0 := by
  have hzero :=
    avram_bvb_phys113_original_BV_ruin_contact_occupation_mark_null
      X hStanding hBV μ U hU
  have hae : ∀ᵐ z ∂X.ν, z ∉
      {z : ℝ | 0 < μ {t : ℝ≥0 | U t = -z}} :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hae] with z hz
  exact le_antisymm (not_lt.mp hz) (by positivity)
