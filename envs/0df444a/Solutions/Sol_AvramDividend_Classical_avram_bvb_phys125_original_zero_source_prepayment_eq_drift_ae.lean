-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys125_original_zero_source_prepayment_eq_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:35:02.460566+00:00
-- url     : https://prove2.me/submissions/3f71768a-b700-4cb8-ba13-26954b8c8135

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The original BV no-jump source prepayment reserve equals
the ordinary controlled drift reserve at almost every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω) :
    ∀ᵐ t ∂μ, 0 < (t : ℝ≥0) →
      Function.leftLim (fun s : ℝ≥0 =>
        x + (s : ℝ) * X.drift - rightLimit D s ω) t =
          x + (t : ℝ) * X.drift - D t ω := by
  have hzero :=
    avram_bvb_phys116_original_admissible_dividend_ae_continuity
      X x C D hD μ ω
  have hae : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => D s ω) t := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hae] with t ht htpos
  have hnb : (nhdsWithin t (Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  rw [avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
    X x C D hD ω t hnb]
  rw [ht.continuousWithinAt.leftLim_eq]
