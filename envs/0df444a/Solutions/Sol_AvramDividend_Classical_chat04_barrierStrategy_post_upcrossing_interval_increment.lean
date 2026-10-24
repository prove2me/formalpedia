-- Prove2me | solution 1 for AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:31:13.043+00:00
-- url     : https://prove2.me/submissions/49e7ae27-bdc7-41da-9ac0-8a476a92c79f

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_record_increment
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Barrier and record increments agree on every interval after first upcrossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω)
    (u r s : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (v : ℝ≥0) (_ : a - x < X.X v ω), (v : ℝ≥0∞)))
    (hur : u ≤ r) (hrs : r ≤ s)
    (hb : BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc 0 s)) :
    barrierStrategy X x a s ω - barrierStrategy X x a r ω =
      runningSup X s ω - runningSup X r ω := by
  have hus : u ≤ s := hur.trans hrs
  have hsr : u + (s - u) = s := add_tsub_cancel_of_le hus
  have hrr : u + (r - u) = r := add_tsub_cancel_of_le hur
  have hb_r : BddAbove
      ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc 0 r) :=
    hb.mono (Set.image_mono (Set.Icc_subset_Icc_right hrs))
  have hsval : barrierStrategy X x a s ω =
      runningSup X s ω - runningSup X u ω := by
    simpa only [hsr] using
      (chat04_barrierStrategy_post_upcrossing_record_increment
        X x a hxa u (s - u) ω hu (by simpa only [hsr] using hb))
  have hrval : barrierStrategy X x a r ω =
      runningSup X r ω - runningSup X u ω := by
    simpa only [hrr] using
      (chat04_barrierStrategy_post_upcrossing_record_increment
        X x a hxa u (r - u) ω hu (by simpa only [hrr] using hb_r))
  rw [hsval, hrval]
  ring
