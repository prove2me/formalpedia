-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_nnreal_left_continuous_borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:16:06.443206+00:00
-- url     : https://prove2.me/submissions/156c233f-5571-45e8-95c9-f185804d2b68

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_floor_grid_le_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem solution
    (g : ℝ≥0 → ℝ) (hg : ∀ t : ℝ≥0, ContinuousWithinAt g (Iic t) t) :
    Measurable g := by
  classical
  let q (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
    ⟨(⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1), by positivity⟩
  have hmeas (n : ℕ) : Measurable (fun t => g (q n t)) := by
    exact (measurable_of_countable (fun k : ℕ =>
      g (⟨(k : ℝ) / ((n : ℝ) + 1), by positivity⟩ : ℝ≥0))).comp
      ((continuous_subtype_val.measurable.mul_const ((n : ℝ) + 1)).nat_floor)
  have hlim (t : ℝ≥0) : Tendsto (fun n => g (q n t)) atTop (nhds (g t)) := by
    have hq : (∀ n, q n t ≤ t) ∧ Tendsto (fun n => q n t) atTop (nhds t) :=
      AvramDividend.Classical.avram_chat24_floor_grid_le_tendsto t
    have hw : Tendsto (fun n => q n t) atTop (𝓝[≤] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hq.2, Filter.Eventually.of_forall hq.1⟩
    exact (hg t).tendsto.comp hw
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 hlim)
