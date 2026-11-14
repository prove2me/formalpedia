-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB270_original_fixed_level_finite_horizon_joint_hit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:11.887453+00:00
-- url     : https://prove2.me/submissions/e0368af5-66e0-417f-bb16-a824c2c0f6d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section

/-- The original fixed-level reserve hit event is jointly measurable on each finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    MeasurableSet {z : ℝ × Ω |
      0 < z.1 ∧ z.1 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.1) z.2 -
          rightLimit D (Real.toNNReal z.1) z.2 = b} := by
  have hJoint :=
    avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD
  have hPair : Measurable
      (fun z : ℝ × Ω => (Real.toNNReal z.1, z.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hF : Measurable
      (fun z : ℝ × Ω =>
        x + X.X (Real.toNNReal z.1) z.2 -
          rightLimit D (Real.toNNReal z.1) z.2) :=
    hJoint.comp hPair
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_eq_fun hF measurable_const))
