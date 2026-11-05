-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_submeasure_null_singletons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:58:19.382228+00:00
-- url     : https://prove2.me/submissions/37430cab-f33f-4474-8394-725c5ac52e94

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Restricting the actual original Stieltjes measure away from all its
positive singleton-mass payment times leaves zero mass at every singleton. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D) :
    ∀ (ω : Ω) (t : ℝ),
      ((dividendMeasure D ω).restrict
        {s : ℝ | ¬0 < dividendMeasure D ω {s}}) {t} = 0 := by
  intro ω t
  rw [Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : 0 < dividendMeasure D ω {t}
  · have hp : dividendMeasure D ω {t} ≠ 0 := ne_of_gt ht
    have hset : ({t} : Set ℝ) ∩
        {s : ℝ | ¬0 < dividendMeasure D ω {s}} = ∅ := by
      ext u
      by_cases hu : u = t
      · subst u
        simp [hp]
      · simp [hu]
    rw [hset]
    simp
  · have hz : dividendMeasure D ω {t} = 0 :=
      le_antisymm (not_lt.mp ht) zero_le
    have hset : ({t} : Set ℝ) ∩
        {s : ℝ | ¬0 < dividendMeasure D ω {s}} = {t} := by
      ext u
      by_cases hu : u = t
      · subst u
        simp [hz]
      · simp [hu]
    rw [hset]
    exact hz
