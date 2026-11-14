-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB307_original_good_cell_fixed_level_hit_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:01:24.400001+00:00
-- url     : https://prove2.me/submissions/2de5084d-6b55-4ee1-849a-0f8d1145fef7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

/-- One original Gaussian good-cell hit event is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) :
    MeasurableSet {z : Ω × ℝ |
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b} := by
  have hPair : Measurable
      (fun z : Ω × ℝ => (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hR : Measurable
      (fun z : Ω × ℝ => x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1) :=
    (avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD).comp hPair
  have hDTime (t : ℝ≥0) : Measurable (D t) :=
    (hD.2.2.2 t).mono (𝓕.le t) le_rfl
  have hInc : Measurable (fun z : Ω × ℝ =>
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1) :=
    ((hDTime _).comp measurable_fst).sub
      ((hDTime _).comp measurable_fst)
  exact (measurableSet_Ioo.preimage measurable_snd).inter
    ((measurableSet_le hInc measurable_const).inter
      (measurableSet_eq_fun hR measurable_const))
