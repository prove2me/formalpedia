-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_full_hjb_from_interior_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:08:44.477672+00:00
-- url     : https://prove2.me/submissions/53623161-68fd-47ab-9fb8-0ffe76b5c09e

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
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

/-- Exact original-source HJB assembly from interior compensated harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  by_cases hcpos : 0 < cstar W
  · intro y hy
    rcases lt_trichotomy y (cstar W).toReal with hlt | heq | hgt
    · have hvalue := hinside hcpos y (mem_Ioo.mpr ⟨hy, hlt⟩)
      have hgrad := (vcstar_deriv_ge_one X hX q hq W hW y hy).2
      refine ⟨hvalue.1, ?_⟩
      rw [hvalue.2]
      exact max_eq_left (by linarith)
    · subst y
      exact vcstar_hjb_at_positive_cstar
        X hX q hq W hW hc h_smooth hcpos hgen
    · exact vcstar_hjb_above_cstar_of_generator X q W hgen y hgt
  · have hc0 : cstar W = 0 :=
      le_antisymm (not_lt.mp hcpos) bot_le
    exact vcstar_hjb_all_positive_of_generator_zero_barrier X q W hc0 hgen
