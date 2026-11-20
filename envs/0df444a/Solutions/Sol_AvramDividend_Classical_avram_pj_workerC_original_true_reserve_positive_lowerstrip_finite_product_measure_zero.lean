-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_true_reserve_positive_lowerstrip_finite_product_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:21:27.811224+00:00
-- url     : https://prove2.me/submissions/4a207163-6bc3-4381-ac37-9acdd3774a4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μ] :
    Tendsto (fun k : ℕ =>
      μ {p : ℝ≥0 × Ω |
          0 < riskProcess X x D p.1 p.2 ∧
          riskProcess X x D p.1 p.2 ≤
            (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let Y : (ℝ≥0 × Ω) → ℝ :=
    fun p => riskProcess X x D p.1 p.2
  have hYm : Measurable Y :=
    avram_p3_g2_original_prepayment_riskProcess_joint_measurable
      X x D hD.1.1
  let S : ℕ → Set (ℝ≥0 × Ω) := fun k =>
    {p : (ℝ≥0 × Ω) | 0 < Y p ∧ Y p ≤ (1 : ℝ) / ((k : ℝ) + 1)}
  have hMeas : ∀ k, MeasurableSet (S k) := by
    intro k
    exact (measurableSet_lt measurable_const hYm).inter
      (measurableSet_le hYm measurable_const)
  have hAnti : Antitone S := by
    intro i j hij p hp
    refine ⟨hp.1, le_trans hp.2 ?_⟩
    gcongr
  have hEmpty : (⋂ k, S k) = (∅ : Set (ℝ≥0 × Ω)) := by
    ext p
    constructor
    · intro hp
      have hP : 0 < Y p := (Set.mem_iInter.mp hp 0).1
      have hAll : ∀ k : ℕ,
          Y p ≤ (1 : ℝ) / ((k : ℝ) + 1) :=
        fun k => (Set.mem_iInter.mp hp k).2
      have hLimit : Y p ≤ 0 :=
        ge_of_tendsto
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          (Filter.Eventually.of_forall hAll)
      exact False.elim ((not_le_of_gt hP) hLimit)
    · simp
  have hFinite : ∃ k, μ (S k) ≠ ⊤ := by
    exact ⟨0, ne_of_lt (measure_lt_top μ (S 0))⟩
  have hTend :=
    MeasureTheory.tendsto_measure_iInter_atTop
      (fun k => (hMeas k).nullMeasurableSet) hAnti hFinite
  change Tendsto (μ ∘ S) atTop (𝓝 (0 : ℝ≥0∞))
  simpa only [hEmpty, measure_empty] using hTend
