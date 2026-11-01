-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:14:27.453389+00:00
-- url     : https://prove2.me/submissions/e75d24c8-1286-4da9-a012-2883101e9d9a

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An exact source HJB supersolution needs interior superharmonicity, not equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0 := by
  have hc := cstar_lt_top X hX q hq W hW
  have hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0 := by
    intro y hy
    exact ⟨vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW y hy, hres_above y hy⟩
  by_cases hcpos : 0 < cstar W
  · intro y hy
    rcases lt_trichotomy y (cstar W).toReal with hlt | heq | hgt
    · have hvalue := hinside hcpos y (mem_Ioo.mpr ⟨hy, hlt⟩)
      have hgrad := (vcstar_deriv_ge_one X hX q hq W hW y hy).2
      refine ⟨hvalue.1, ?_⟩
      exact max_le hvalue.2 (by linarith)
    · subst y
      have hcap := vcstar_hjb_at_positive_cstar
        X hX q hq W hW hc hsmooth hcpos hgen
      exact ⟨hcap.1, le_of_eq hcap.2⟩
    · have habove := vcstar_hjb_above_cstar_of_generator X q W hgen y hgt
      exact ⟨habove.1, le_of_eq habove.2⟩
  · have hc0 : cstar W = 0 :=
      le_antisymm (not_lt.mp hcpos) bot_le
    intro y hy
    have hall :=
      vcstar_hjb_all_positive_of_generator_zero_barrier X q W hc0 hgen y hy
    exact ⟨hall.1, le_of_eq hall.2⟩
