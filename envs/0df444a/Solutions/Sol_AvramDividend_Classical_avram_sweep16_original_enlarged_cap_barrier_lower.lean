-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_enlarged_cap_barrier_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:56:15.088692+00:00
-- url     : https://prove2.me/submissions/eca66c6c-e7bf-4341-ba9f-3847456a581a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_monotone_cap
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (C : ℝ≥0∞) (hCap : cstar W ≤ C) :
    ∀ x : ℝ, 0 ≤ x →
      ENNReal.ofReal (vcstar W x) ≤ valueFunctionLe X q C x := by
  intro x hx
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hOriginal :
      ENNReal.ofReal (vcstar W x) ≤ valueFunctionLe X q (cstar W) x :=
    (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
      X hX q hq W hW hc x hx).1
  exact hOriginal.trans (valueFunctionLe_monotone_cap X q x (cstar W) C hCap)
