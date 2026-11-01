-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_hjb_of_value_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:58:19.800258+00:00
-- url     : https://prove2.me/submissions/0d2ffb7a-9239-4bfb-b8ff-a7fcad260453

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At either a zero or positive source optimal cap, sufficiently large
candidate value removes the sole positive compensated jump correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hfloor : 1 ≤ vcstar W x)
    (hdrift : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hzero : max 0 (1 - vcstar W x) = 0 :=
    max_eq_left (by linarith)
  have hmass : X.c +
      (X.ν).real (Ioo (-1 : ℝ) (-x)) *
        max 0 (1 - vcstar W x) ≤ q * vcstar W x := by
    simpa [hzero] using hdrift
  exact avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass
    X hX q hq W hW x hx hmass
