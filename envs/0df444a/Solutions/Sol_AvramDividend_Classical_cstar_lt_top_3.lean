-- Prove2me | solution 3 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T19:55:02.925996+00:00
-- url     : https://prove2.me/submissions/6fca62aa-469c-423d-9b6c-faa7aebdef13
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
  rcases scaleDeriv_inf_attained X hX q hq W hW with ⟨a, ha, hmin⟩ | hzero
  · have hne : (cstarSet W).Nonempty := ⟨a, ha, hmin⟩
    rw [cstar, if_pos hne]
    have hle :
        (⨅ b ∈ cstarSet W, ENNReal.ofReal b) ≤ ENNReal.ofReal a :=
      biInf_le (fun b : ℝ => ENNReal.ofReal b) ⟨ha, hmin⟩
    exact hle.trans_lt ENNReal.ofReal_lt_top
  · by_cases hne : (cstarSet W).Nonempty
    · rw [cstar, if_pos hne]
      obtain ⟨a, ha⟩ := hne
      exact (biInf_le (fun b : ℝ => ENNReal.ofReal b) ha).trans_lt
        ENNReal.ofReal_lt_top
    · rw [cstar, if_neg hne, if_pos hzero]
      exact ENNReal.zero_lt_top
