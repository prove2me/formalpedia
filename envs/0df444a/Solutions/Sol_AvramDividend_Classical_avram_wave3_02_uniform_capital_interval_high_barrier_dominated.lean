-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_capital_interval_high_barrier_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:04:35.554024+00:00
-- url     : https://prove2.me/submissions/9cbcbc71-c38f-4dcc-a64f-8cc908f6dd71

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Uniform strictly worse high-barrier dividend values across all capital
reserves separated from zero and bounded from above. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∀ᶠ a : ℝ in atTop, ∀ x : ℝ, δ ≤ x → x ≤ R →
      dividendValue X q x (barrierStrategy X x a) <
        dividendValue X q x (barrierStrategy X x 0) := by
  have hR : 0 ≤ R := (le_of_lt hδ).trans hδR
  have hlim := avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
    X hX q hq W hW R hR
  have hevent : ∀ᶠ a : ℝ in atTop,
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a)) <
          ENNReal.ofReal δ :=
    Filter.Tendsto.eventually_lt_const (ENNReal.ofReal_pos.mpr hδ) hlim
  filter_upwards [hevent] with a ha x hδx hxR
  have hx0 : 0 ≤ x := (le_of_lt hδ).trans hδx
  have hvalue :
      dividendValue X q x (barrierStrategy X x a) ≤
      (⨆ y : ℝ, ⨆ (_ : 0 ≤ y ∧ y ≤ R),
        dividendValue X q y (barrierStrategy X y a)) :=
    le_iSup_of_le x (le_iSup_of_le ⟨hx0, hxR⟩ (le_refl _))
  have hz : dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal x + barrierSupValue X 0 q := by
    simpa using
      (avram_wave3_02_all_nonnegative_barriers_sup X hX q hq W hW
        0 (le_refl (0 : ℝ)) x hx0)
  have hbase : ENNReal.ofReal δ ≤
      dividendValue X q x (barrierStrategy X x 0) := by
    rw [hz]
    exact (ENNReal.ofReal_le_ofReal hδx).trans
      (le_add_of_nonneg_right (zero_le : (0 : ENNReal) ≤ barrierSupValue X 0 q))
  exact (lt_of_le_of_lt hvalue ha).trans_le hbase
