-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_hjb_all_positive_of_signed_band_criterion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:29:08.680515+00:00
-- url     : https://prove2.me/submissions/6583380f-d5a9-4e28-8277-c1d5be65b9e3

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_signed_generator_residual_le_band_mass
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original Lévy HJB on all positive reserves follows from a sharp
two-band scalar balance that explicitly retains large-ruin killing jumps.
No unsupported implication from standing assumptions to this balance is
claimed; the root's exact full-positive C²/BV/Gaussian alternative is kept. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hmass : ∀ y : ℝ, (cstar W).toReal < y →
      X.c + (X.ν).real (Ioo (-1 : ℝ) (-y)) *
        max 0 (1 - vcstar W y) -
        (X.ν).real (Iic (-1 : ℝ) ∩ Iio (-y)) * vcstar W y ≤
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
      avram_wave4_05_source_signed_generator_residual_le_band_mass
        X hX q hq W hW y hy
    exact ⟨hdom, by linarith [hmass y hy]⟩
  exact vcstar_hjb_all_positive_of_generator
    X hX q hq W hW hcfin h_smooth hgen
