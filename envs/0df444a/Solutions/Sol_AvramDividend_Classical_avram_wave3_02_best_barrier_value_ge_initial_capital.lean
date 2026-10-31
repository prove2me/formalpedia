-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_best_barrier_value_ge_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:15:26.061776+00:00
-- url     : https://prove2.me/submissions/2ba9f142-dba3-4ed4-847f-de51161b6951

import Mathlib.Data.ENNReal.Real
import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The best genuine constant-barrier dividend reward always dominates
immediate withdrawal of the initial nonnegative capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal x ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) := by
  have hz : dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal x + barrierSupValue X 0 q := by
    simpa using
      (avram_wave3_02_all_nonnegative_barriers_sup X hX q hq W hW
        0 (le_refl (0 : ℝ)) x hx)
  have hle : ENNReal.ofReal x ≤
      dividendValue X q x (barrierStrategy X x 0) := by
    rw [hz]
    calc
      ENNReal.ofReal x = ENNReal.ofReal x + 0 := (add_zero _).symm
      _ ≤ ENNReal.ofReal x + barrierSupValue X 0 q :=
        add_le_add_right
          (show (0 : ENNReal) ≤ barrierSupValue X 0 q from zero_le) _
  exact le_iSup_of_le (0 : ℝ)
    (le_iSup_of_le (le_refl (0 : ℝ)) hle)
