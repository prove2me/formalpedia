-- Prove2me | solution 13 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:51:29.648857+00:00
-- url     : https://prove2.me/submissions/ef9bdfbb-ed14-4d93-b6e1-ffdc6ccd1604
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact published cstar_lt_top target; conditional on the still-Open
    scaleDeriv_inf_attained theorem. A proof-sketch until that child is Proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  classical
  by_cases hne : (cstarSet W).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hne' : (cstarSet W).Nonempty := ⟨a, ha⟩
    rw [cstar, if_pos hne']
    exact lt_of_le_of_lt (iInf₂_le a ha) ENNReal.ofReal_lt_top
  · rcases scaleDeriv_inf_attained X hX q hq W hW with
      ⟨a, ha, hmin⟩ | hzero
    · exact False.elim (hne ⟨a, ha, hmin⟩)
    · rw [cstar, if_neg hne, if_pos hzero]
      exact ENNReal.zero_lt_top
