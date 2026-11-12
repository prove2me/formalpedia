-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys129_original_drift_reserve_ae_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:54:14.064734+00:00
-- url     : https://prove2.me/submissions/5553da88-3ecc-4748-9909-3529ec1b9cdb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The deterministic-drift reserve corresponding to the original
admissible dividend path is continuous at almost every time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) :
    ∀ᵐ t ∂μ, ContinuousAt
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift - D s ω) t := by
  have hzero :=
    avram_bvb_phys116_original_admissible_dividend_ae_continuity
      X x C D hD μ ω
  have hae : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => D s ω) t := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hae] with t ht
  have hlin : ContinuousAt
      (fun s : ℝ≥0 => x + (s : ℝ) * X.drift) t := by
    fun_prop
  exact hlin.sub ht
