-- Prove2me | solution 2 for AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:51:04.75326+00:00
-- url     : https://prove2.me/submissions/e6f7e869-407a-4d8e-a8f9-7f6fb956aab7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_capped_admissible_of_regular
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by
  have hbase :
      IsAdmissibleLe X a (ENNReal.ofReal a) (barrierStrategy X a a) :=
    AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular
      X a ha.le
      (AvramDividend.Classical.barrierStrategy_left_continuous X a)
      (AvramDividend.Classical.barrierStrategy_right_continuous X a)
      (AvramDividend.Classical.barrierStrategy_adapted X a)
  have hadd :=
    (AvramDividend.Classical.add_initial_excess_admissible_value
      X q x a ha.le hax (barrierStrategy X a a) hbase).2
  have hboundary :=
    AvramDividend.Classical.barrier_strategy_value
      X hX q hq W hW a ha a ha.le le_rfl
  have hderiv : 0 ≤ deriv W a := by
    have hwithin : 0 ≤ derivWithin W (Ici 0) a :=
      hW.2.2.2.1.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ha)] at hwithin
    exact hwithin
  have hWa : 0 ≤ W a := hW.2.1 a ha.le
  have hratio : 0 ≤ W a / deriv W a := div_nonneg hWa hderiv
  rw [AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
    X x a ha.le hax]
  calc
    dividendValue X q x
        (fun t ω => if t = 0 then 0 else (x - a) + barrierStrategy X a a t ω) =
        ENNReal.ofReal (x - a) +
          dividendValue X q a (barrierStrategy X a a) := hadd
    _ = ENNReal.ofReal (x - a) + ENNReal.ofReal (W a / deriv W a) := by
      rw [hboundary]
    _ = ENNReal.ofReal ((x - a) + W a / deriv W a) := by
      symm
      exact ENNReal.ofReal_add (sub_nonneg.mpr hax.le) hratio
    _ = ENNReal.ofReal (barrierValue W a x) := by
      have hx0 : 0 ≤ x := ha.le.trans hax.le
      have hxnot : ¬ x < 0 := by linarith
      simp [barrierValue, scaleDeriv, divE, hxnot,
        not_le.mpr hax, ne_of_gt ha]
