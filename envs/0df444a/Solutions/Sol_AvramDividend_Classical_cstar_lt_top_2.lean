-- Prove2me | solution 2 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T19:45:43.756465+00:00
-- url     : https://prove2.me/submissions/7d0d3fdc-e98a-4e81-9d18-b3c35bd03958
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
  have hfinite (hne : (cstarSet W).Nonempty) :
      (⨅ b ∈ cstarSet W, ENNReal.ofReal b) < ⊤ := by
    obtain ⟨a, ha⟩ := hne
    have hle :
        (⨅ b ∈ cstarSet W, ENNReal.ofReal b) ≤ ENNReal.ofReal a := by
      exact iInf_le_of_le a (iInf_le_of_le ha le_rfl)
    exact hle.trans_lt ENNReal.ofReal_lt_top
  rcases scaleDeriv_inf_attained X hX q hq W hW with hmin | hzero
  · obtain ⟨a, ha, hamin⟩ := hmin
    have hne : (cstarSet W).Nonempty := ⟨a, ha, hamin⟩
    rw [cstar, if_pos hne]
    exact hfinite hne
  · by_cases hne : (cstarSet W).Nonempty
    · rw [cstar, if_pos hne]
      exact hfinite hne
    · rw [cstar, if_neg hne, if_pos hzero]
      exact ENNReal.zero_lt_top
