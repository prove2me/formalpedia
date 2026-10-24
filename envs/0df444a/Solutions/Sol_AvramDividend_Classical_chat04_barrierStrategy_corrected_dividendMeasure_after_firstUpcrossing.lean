-- Prove2me | solution 1 for AvramDividend.Classical.chat04_barrierStrategy_corrected_dividendMeasure_after_firstUpcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:21:39.287985+00:00
-- url     : https://prove2.me/submissions/7f2b3271-3736-4acf-b3d6-a9b66faa545d

import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_record_increment
import Theorems.Thm_AvramDividend_Classical_chat04_stieltjes_Ioc_eq_of_right_continuous_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A barrier dividend interval equals the original running-record interval after crossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (ha0 : 0 ≤ a) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) := by
  have hD := barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx0 ha0
  have hE := runningSup_isDividendStrategy X
  have hmD : Monotone (fun r => barrierStrategy X x a r ω) := hD.2.1 ω
  have hmE : Monotone (fun r => runningSup X r ω) :=
    (runningSup_monotone_and_path_le X ω).1
  have hrD (r : ℝ≥0) :
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Set.Ici r) r :=
    barrierStrategy_right_continuous_below_barrier X x a hx0 ha0 hxa ω r
  have hEq : (fun r : ℝ≥0 => barrierStrategy X (0 : ℝ) 0 r ω) =
      (fun r : ℝ≥0 => runningSup X r ω) := by
    funext r
    exact barrierStrategy_self_eq_runningSup X 0 ω r
  have hrE (r : ℝ≥0) :
      ContinuousWithinAt (fun s => runningSup X s ω) (Set.Ici r) r := by
    simpa only [hEq] using (barrierStrategy_right_continuous X 0 ω r)
  have hinc : barrierStrategy X x a (u + t) ω -
        barrierStrategy X x a u ω =
      runningSup X (u + t) ω - runningSup X u ω := by
    rw [chat04_barrierStrategy_post_upcrossing_record_increment X x a hxa u t ω hu hb]
    rw [barrierStrategy_zero_at_firstUpcrossing X x a hxa ω u hu]
    simp
  exact chat04_stieltjes_Ioc_eq_of_right_continuous_increment
    (barrierStrategy X x a) (runningSup X) hD hE ω u (u + t)
    hmD hmE (hrD u) (hrD (u + t)) (hrE u) (hrE (u + t)) hinc
