-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:58:26.549285+00:00
-- url     : https://prove2.me/submissions/a22f4690-12aa-4b47-ab32-b0f06e8c91ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original dividend Stieltjes measure decomposes exactly into its
positive singleton-mass and complementary parts. This is an identity of
measures, so it also preserves initial and closed-horizon payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ ω : Ω,
      (dividendMeasure D ω).restrict
          {t : ℝ | 0 < dividendMeasure D ω {t}} +
      (dividendMeasure D ω).restrict
          {t : ℝ | ¬0 < dividendMeasure D ω {t}} =
        dividendMeasure D ω := by
  intro ω
  have hgraph :=
    avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
      D hD
  have hs : MeasurableSet
      {t : ℝ | 0 < dividendMeasure D ω {t}} := by
    have hpre := hgraph.preimage
      ((measurable_const : Measurable (fun _ : ℝ => ω)).prodMk measurable_id)
    simpa only [Set.preimage, Set.mem_setOf_eq, id_eq] using hpre
  exact Measure.restrict_add_restrict_compl hs
