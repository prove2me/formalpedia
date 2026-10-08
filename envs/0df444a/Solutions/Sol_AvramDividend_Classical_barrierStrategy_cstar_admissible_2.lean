-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_cstar_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:55:49.423813+00:00
-- url     : https://prove2.me/submissions/51ef696d-1592-45f4-959b-7c42d9773d78

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

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (W : ℝ → ℝ) (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) := by
  intro x hx
  have hfinite : cstar W ≠ ⊤ := ne_of_lt hc
  have hcap : ENNReal.ofReal (cstar W).toReal = cstar W :=
    ENNReal.ofReal_toReal hfinite
  have hadm :=
    AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
      X x (cstar W).toReal hx ENNReal.toReal_nonneg
  rw [hcap] at hadm
  exact hadm
