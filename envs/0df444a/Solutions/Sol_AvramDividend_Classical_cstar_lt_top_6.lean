-- Prove2me | solution 6 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:56:17.036359+00:00
-- url     : https://prove2.me/submissions/29feac66-32d9-49a6-a393-34cd32606427
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
  have hmin := scaleDeriv_inf_attained X hX q hq W hW
  by_cases hne : (cstarSet W).Nonempty
  · rcases hne with ⟨a, ha⟩
    rw [cstar, if_pos ⟨a, ha⟩]
    exact lt_of_le_of_lt (iInf₂_le a ha) ENNReal.ofReal_lt_top
  · rw [cstar, if_neg hne]
    by_cases hzero :
        ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)
    · rw [if_pos hzero]
      exact ENNReal.zero_lt_top
    · rcases hmin with ⟨a, ha, hall⟩ | hz
      · exact False.elim (hne ⟨a, ha, hall⟩)
      · exact False.elim (hzero hz)
