-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:03:27.532868+00:00
-- url     : https://prove2.me/submissions/63af6d7c-9a49-44da-abcd-3795204a8197

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact source small-ruin overshoot has a genuine L1 jump kernel:
finite Levy intensity away from the origin replaces any first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) :
    Integrable
      ((Ioo (-1 : ℝ) (-x)).indicator
        (fun y : ℝ => max 0 (-vcstar W x - y))) X.ν := by
  have hsub : Ioo (-1 : ℝ) (-x) ⊆ Iic (-x) := by
    intro y hy
    exact le_of_lt hy.2
  have hfin : X.ν (Ioo (-1 : ℝ) (-x)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (negative_jump_truncation_measure_finite X.ν hνint x hx)
  apply (integrable_indicator_iff measurableSet_Ioo).2
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => max 0 (-vcstar W x - y))
      (X.ν.restrict (Ioo (-1 : ℝ) (-x))) := by fun_prop
  refine IntegrableOn.of_bound hfin hmeas (max 0 (1 - vcstar W x)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hnonneg : 0 ≤ max 0 (-vcstar W x - y) := le_max_left _ _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact max_le_max_left 0 (by linarith [hy.1])
