-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_ruin_criterion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:48:21.691801+00:00
-- url     : https://prove2.me/submissions/1fad18dd-3ff3-4f5c-a5e6-7a5f2ec86a70

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_full_generator_signed_ruin_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine compensated Lévy HJB on positive reserves follows from
the exact signed ruin-jump balance, retaining the possible zero-reserve
landing atom and the full short-ruin overshoot integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hsigned : ∀ y : ℝ, (cstar W).toReal < y →
      X.c + (∫ z in Ioo (-1 : ℝ) (-y),
        (-vcstar W y - z) ∂X.ν) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-y)) * vcstar W y +
        (X.ν).real ({-y} : Set ℝ) *
          (vcstar W 0 - vcstar W y + if y < 1 then y else 0) ≤
        q * vcstar W y) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  have hcfin : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0 := by
    intro y hy
    obtain ⟨hdom, hres⟩ :=
      avram_wave4_05_source_full_generator_signed_ruin_bound
        X hX q hq W hW y hy
    exact ⟨hdom, by linarith [hsigned y hy]⟩
  exact vcstar_hjb_all_positive_of_generator
    X hX q hq W hW hcfin h_smooth hgen
