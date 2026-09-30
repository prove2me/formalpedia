-- Prove2me | solution 4 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T19:55:04.117761+00:00
-- url     : https://prove2.me/submissions/2802fc5c-3cce-4ad0-8d77-6947d42fbc75
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
  by_cases hne : (cstarSet W).Nonempty
  · rw [cstar, if_pos hne]
    obtain ⟨a, ha⟩ := hne
    calc
      (⨅ b ∈ cstarSet W, ENNReal.ofReal b)
          ≤ ENNReal.ofReal a :=
        biInf_le (fun b : ℝ => ENNReal.ofReal b) ha
      _ < ⊤ := ENNReal.ofReal_lt_top
  · have hzero :
        ∀ x : ℝ, 0 < x →
          derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
      rcases scaleDeriv_inf_attained X hX q hq W hW with hmin | hzero
      · obtain ⟨a, ha, hamin⟩ := hmin
        exfalso
        exact hne ⟨a, ha, hamin⟩
      · exact hzero
    rw [cstar, if_neg hne, if_pos hzero]
    exact ENNReal.zero_lt_top
