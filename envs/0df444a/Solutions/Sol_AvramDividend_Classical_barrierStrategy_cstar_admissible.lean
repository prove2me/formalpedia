-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_cstar_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:02:30.09899+00:00
-- url     : https://prove2.me/submissions/84e5d7f8-5a49-4771-91d2-fb7cfa01dd75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (W : ℝ → ℝ) (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) := by
  intro x hx
  have ha : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have h :=
    AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
      X x (cstar W).toReal hx ha
  have hne : cstar W ≠ ⊤ := ne_of_lt hc
  simpa only [ENNReal.ofReal_toReal hne] using h
