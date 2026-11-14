-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB298_original_bad_grid_hit_event_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:56:09.598435+00:00
-- url     : https://prove2.me/submissions/a734a91e-7f82-4c16-b59d-6ca8c47e720b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Original localised bad-dividend physical grid hit event is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n m M : ℕ) :
    MeasurableSet {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      1 / ((m : ℝ) ^ 3) <
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)} := by
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
  have hInc (i : ℕ) : Measurable (fun z : Ω × ℝ =>
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1) :=
    ((hDTime _).comp measurable_fst).sub
      ((hDTime _).comp measurable_fst)
  have hTerm : Measurable (fun z : Ω × ℝ =>
      D n z.1 - D 0 z.1) :=
    ((hDTime _).comp measurable_fst).sub
      ((hDTime _).comp measurable_fst)
  have hOne (i : ℕ) : MeasurableSet {z : Ω × ℝ |
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      1 / ((m : ℝ) ^ 3) <
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)} := by
    exact (measurableSet_Ioo.preimage measurable_snd).inter
      ((measurableSet_lt measurable_const (hInc i)).inter
        ((measurableSet_eq_fun hR measurable_const).inter
          (measurableSet_le hTerm measurable_const)))
  have hUnion : MeasurableSet (⋃ i ∈ Finset.range (n * m ^ 4),
    {z : Ω × ℝ |
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      1 / ((m : ℝ) ^ 3) <
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)}) :=
    MeasurableSet.iUnion (fun i : ℕ =>
      MeasurableSet.iUnion (fun _hi : i ∈ Finset.range (n * m ^ 4) => hOne i))
  have hEq : {z : Ω × ℝ | ∃ i ∈ Finset.range (n * m ^ 4),
      z.2 ∈ Set.Ioo
        ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
      1 / ((m : ℝ) ^ 3) <
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
      x + X.X (Real.toNNReal z.2) z.1 -
        rightLimit D (Real.toNNReal z.2) z.1 = b ∧
      D n z.1 - D 0 z.1 ≤ (M : ℝ)} =
      (⋃ i ∈ Finset.range (n * m ^ 4),
        {z : Ω × ℝ |
          z.2 ∈ Set.Ioo
            ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
            (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))) ∧
          1 / ((m : ℝ) ^ 3) <
            D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
            D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
          x + X.X (Real.toNNReal z.2) z.1 -
            rightLimit D (Real.toNNReal z.2) z.1 = b ∧
          D n z.1 - D 0 z.1 ≤ (M : ℝ)}) := by
    ext z
    constructor
    · rintro ⟨i, hi, ht, hinc, hhit, hloc⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨hi, ⟨ht, hinc, hhit, hloc⟩⟩⟩
    · intro hz
      obtain ⟨i, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hi, hcell⟩ := Set.mem_iUnion.mp hz
      obtain ⟨ht, hinc, hhit, hloc⟩ := hcell
      exact ⟨i, hi, ht, hinc, hhit, hloc⟩
  rw [hEq]
  exact hUnion
