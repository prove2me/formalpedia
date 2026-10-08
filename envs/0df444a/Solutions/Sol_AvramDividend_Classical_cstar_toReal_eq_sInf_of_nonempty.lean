-- Prove2me | solution 1 for AvramDividend.Classical.cstar_toReal_eq_sInf_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:52:50.402359+00:00
-- url     : https://prove2.me/submissions/c6dd5b7c-4d7a-4578-a70f-f3ee1d59e281

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open MeasureTheory Set
open scoped NNReal ENNReal

/-- Converts the canonical extended-real definition of the barrier to the
real infimum of positive derivative minimisers. -/
theorem solution (W : ℝ → ℝ) (hS : (cstarSet W).Nonempty) :
    (cstar W).toReal = sInf (cstarSet W) := by
  rw [cstar, if_pos hS, iInf_subtype', ENNReal.toReal_iInf]
  · calc
      (⨅ a : cstarSet W, (ENNReal.ofReal (a : ℝ)).toReal)
          = ⨅ a : cstarSet W, (a : ℝ) := by
              apply iInf_congr
              intro a
              rw [ENNReal.toReal_ofReal]
              exact le_of_lt (by simpa [cstarSet] using a.property.1)
      _ = sInf (cstarSet W) := (sInf_eq_iInf' _).symm
  · intro a
    exact ENNReal.ofReal_ne_top
