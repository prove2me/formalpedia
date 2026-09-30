-- Prove2me | solution 8 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:56:18.261296+00:00
-- url     : https://prove2.me/submissions/32c71367-e2b8-4ec5-bec4-88c508fda281
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  rcases scaleDeriv_inf_attained X hX q hq W hW with hpos | hzero
  · rcases hpos with ⟨a, ha, hmin⟩
    have hne : (cstarSet W).Nonempty := ⟨a, ha, hmin⟩
    rw [cstar, if_pos hne]
    exact lt_of_le_of_lt (iInf₂_le a ⟨ha, hmin⟩) ENNReal.ofReal_lt_top
  · by_cases hne : (cstarSet W).Nonempty
    · rcases hne with ⟨a, ha⟩
      rw [cstar, if_pos ⟨a, ha⟩]
      exact lt_of_le_of_lt (iInf₂_le a ha) ENNReal.ofReal_lt_top
    · rw [cstar, if_neg hne]
      rw [if_pos hzero]
      exact ENNReal.zero_lt_top
