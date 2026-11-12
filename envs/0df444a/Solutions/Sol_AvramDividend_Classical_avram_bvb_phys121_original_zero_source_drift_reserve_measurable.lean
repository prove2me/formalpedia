-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys121_original_zero_source_drift_reserve_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:14:10.860195+00:00
-- url     : https://prove2.me/submissions/31df93a8-d359-47c3-b242-92bde9a271a0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The original BV no-source-jump controlled reserve is a Borel
time function; this is the integrand path underlying phys95. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 =>
      x + (t : ℝ) * X.drift - rightLimit D t ω) := by
  have hright :=
    avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
      X x C D hD ω
  have hlinear : Measurable (fun t : ℝ≥0 => x + (t : ℝ) * X.drift) := by
    fun_prop
  exact hlinear.sub hright
