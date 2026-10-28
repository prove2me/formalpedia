-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:48:17.250982+00:00
-- url     : https://prove2.me/submissions/b5bf44ec-c404-43c0-b683-ec04308c4829
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Global HJB assembly from below-barrier and barrier-point verification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  by_cases hzero : cstar W = 0
  · exact vcstar_hjb_all_positive_of_generator_zero_barrier
      X q W hzero hgen
  · have hpos : 0 < cstar W := pos_iff_ne_zero.mpr hzero
    have hbelow :=
      vcstar_hjb_below_positive_cstar
        X hX q hq W hW hc h_smooth hpos
    have hat :=
      vcstar_hjb_at_positive_cstar
        X hX q hq W hW hc h_smooth hpos hgen
    have habove := vcstar_hjb_above_cstar_of_generator X q W hgen
    intro y hy
    rcases lt_trichotomy y (cstar W).toReal with hlt | heq | hgt
    · exact hbelow y hy
        ((ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy)
          (ne_of_lt hc)).mpr hlt)
    · simpa only [heq] using hat
    · exact habove y hgt
