-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_predictable_reciprocal_band_mark_kernel_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:23:40.402809+00:00
-- url     : https://prove2.me/submissions/5c274e5d-365e-4afa-a647-671097960689

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let F : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ T ∧ p.2 ∈ B then p.2 else 0
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F ∧
    (∀ p, |F p| ≤ (1 : ℝ)) := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let F : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if 0 < p.1.1 ∧ p.1.1 ≤ T ∧ p.2 ∈ B then p.2 else 0
  change Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F ∧
    (∀ p, |F p| ≤ (1 : ℝ))
  constructor
  · letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable
    have hT :=
      avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
    have h0 :=
      avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 0
    have hPos : MeasurableSet
        {p : ((ℝ≥0 × Ω) × ℝ) | 0 < p.1.1} := by
      convert h0.compl using 1
      ext p
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    have hMark : MeasurableSet
        {p : ((ℝ≥0 × Ω) × ℝ) | p.2 ∈ B} :=
      measurableSet_Ioc.preimage measurable_snd
    have hPred : MeasurableSet
        {p : ((ℝ≥0 × Ω) × ℝ) |
          0 < p.1.1 ∧ p.1.1 ≤ T ∧ p.2 ∈ B} := by
      convert (hPos.inter hT).inter hMark using 1
      ext p
      simp [and_assoc]
    exact measurable_snd.ite hPred measurable_const
  · intro p
    dsimp [F]
    split_ifs with h
    · have hz : p.2 < 0 := by
        have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
        exact lt_of_le_of_lt h.2.2.2 (neg_neg_of_pos hm)
      have hn0 : 0 < ((n : ℝ) + 1) := by positivity
      have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ hn0).mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      rw [abs_of_neg hz]
      have hl := h.2.2.1
      linarith
    · simp
