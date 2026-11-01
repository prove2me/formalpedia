-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_part_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:39:45.324248+00:00
-- url     : https://prove2.me/submissions/37bdf84f-86a0-4392-a3b7-2b11f1a36a0c

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_jump_part_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_zero_cap_positive_jump_part_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For every finite source optimal cap, including the zero cap,
the entire positive compensated jump kernel is the strict ruin overshoot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (y : ℝ) (hy : y < 0) :
    max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) =
      if y ∈ Ioo (-1 : ℝ) (-x)
      then max 0 (-vcstar W x - y) else 0 := by
  have hcfin : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  by_cases hc0 : cstar W = 0
  · have hx0 : 0 < x := by simpa [hc0] using hx
    exact avram_wave4_05_source_zero_cap_positive_jump_part_exact
      X hX q hq W hW hc0 x hx0 y hy
  · have hcpos : 0 < cstar W :=
      lt_of_le_of_ne zero_le (Ne.symm hc0)
    have hpos : 0 < (cstar W).toReal :=
      ENNReal.toReal_pos_iff.mpr ⟨hcpos, hcfin⟩
    exact avram_wave4_05_source_positive_jump_part_exact
      X hX q hq W hW hpos x hx y hy
