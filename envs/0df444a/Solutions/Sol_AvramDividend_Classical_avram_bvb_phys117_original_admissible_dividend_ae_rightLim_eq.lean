-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys117_original_admissible_dividend_ae_rightLim_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:58:20.035208+00:00
-- url     : https://prove2.me/submissions/6ae69ed2-9b3b-448a-aa97-aeaabcaff8ba

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- For an original admissible dividend strategy, its strict right
limit agrees with the physical dividend path almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω) :
    ∀ᵐ t ∂μ,
      Function.rightLim (fun s : ℝ≥0 => D s ω) t = D t ω := by
  have hzero :=
    avram_bvb_phys116_original_admissible_dividend_ae_continuity
      X x C D hD μ ω
  have hae : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => D s ω) t := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hae] with t ht
  exact ht.continuousWithinAt.rightLim_eq
