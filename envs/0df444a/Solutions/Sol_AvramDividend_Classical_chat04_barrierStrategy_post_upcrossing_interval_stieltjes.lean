-- Prove2me | solution 1 for AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:54:55.786122+00:00
-- url     : https://prove2.me/submissions/d51ce96f-ca80-4f8d-8ed7-3f5b650fb181

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_interval_increment
import Theorems.Thm_AvramDividend_Classical_chat04_stieltjes_Ioc_eq_of_right_continuous_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (ha0 : 0 ≤ a) (hxa : x ≤ a)
    (ω : Ω) (u r s : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (v : ℝ≥0) (_ : a - x < X.X v ω), (v : ℝ≥0∞)))
    (hur : u ≤ r) (hrs : r ≤ s)
    (hb : BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc 0 s)) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Ioc (r : ℝ) (s : ℝ)) =
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (r : ℝ) (s : ℝ)) := by
  have hD :=
    AvramDividend.Classical.barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx0 ha0
  have hE :=
    AvramDividend.Classical.runningSup_isDividendStrategy X
  have hmD : Monotone (fun t : ℝ≥0 => barrierStrategy X x a t ω) := hD.2.1 ω
  have hmE : Monotone (fun t : ℝ≥0 => runningSup X t ω) := hE.2.1 ω
  have hinc : barrierStrategy X x a s ω - barrierStrategy X x a r ω =
      runningSup X s ω - runningSup X r ω :=
    AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_increment
      X x a hxa ω u r s hu hur hrs hb
  have hrc : ∀ t : ℝ≥0, ContinuousWithinAt (fun s => runningSup X s ω) (Set.Ici t) t := by
    intro t
    exact AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
      (fun u => X.X u ω) (fun t => runningSup X t ω)
      ((AvramDividend.Classical.runningSup_monotone_and_path_le X ω).1)
      (fun u => (AvramDividend.Classical.runningSup_monotone_and_path_le X ω).2 u)
      (fun t => (AvramDividend.Classical.runningSup_eq_rawSup_nonneg X t ω).1)
      (fun t => X.rightCont ω t) t
  have hrEa : ContinuousWithinAt (fun s => runningSup X s ω) (Set.Ici r) r := hrc r
  have hrEb : ContinuousWithinAt (fun s => runningSup X s ω) (Set.Ici s) s := hrc s
  have hrDa : ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Set.Ici r) r :=
    AvramDividend.Classical.barrierStrategy_right_continuous_below_barrier X x a hx0 ha0 hxa ω r
  have hrDb : ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Set.Ici s) s :=
    AvramDividend.Classical.barrierStrategy_right_continuous_below_barrier X x a hx0 ha0 hxa ω s
  exact AvramDividend.Classical.chat04_stieltjes_Ioc_eq_of_right_continuous_increment
    (barrierStrategy X x a) (runningSup X) hD hE ω r s hmD hmE hrDa hrDb hrEa hrEb hinc
