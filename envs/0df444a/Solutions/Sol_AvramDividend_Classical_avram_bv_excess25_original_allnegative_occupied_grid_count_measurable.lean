-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:58:46.681479+00:00
-- url     : https://prove2.me/submissions/1d3ef7fe-e0d4-42de-8f7e-e198e09b7ee6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- All-mark occupied original negative jump cells form a measurable finite count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        if ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t, X.X t ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ)) ≠ 0 then
          (1 : ℝ≥0∞) else 0) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  have hst : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hm :=
    avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X (u i) (u (i + 1)) hst Set.univ MeasurableSet.univ
  have hset : MeasurableSet {ω : Ω | ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t, X.X t ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ)) ≠ 0} := by
    exact (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hm
  exact Measurable.ite hset measurable_const measurable_const
