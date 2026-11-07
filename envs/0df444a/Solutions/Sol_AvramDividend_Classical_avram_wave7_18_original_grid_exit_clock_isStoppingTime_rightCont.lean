-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:37:43.316107+00:00
-- url     : https://prove2.me/submissions/d0e3458d-dd98-4af9-9d8d-56ea0d82cd61

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_grid_exit_stoppingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (clock : ℕ → ℝ≥0) (hclock : Monotone clock)
    (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => (clock (K ω) : WithTop ℝ≥0)) := by
  have hstop := avram_wave7_18_original_postpayment_grid_exit_stoppingTime
    X x D hD clock H hH lower upper m K hK
  intro t
  have hrep :
      {ω : Ω | (clock (K ω) : WithTop ℝ≥0) ≤ t} =
        ⋃ k : ℕ, {ω : Ω | K ω ≤ k ∧ clock k ≤ t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro ht
      refine ⟨K ω, le_rfl, ?_⟩
      exact WithTop.coe_le_coe.mp ht
    · rintro ⟨k, hKle, hct⟩
      exact WithTop.coe_le_coe.mpr ((hclock hKle).trans hct)
  rw [hrep]
  apply MeasurableSet.iUnion
  intro k
  by_cases hct : clock k ≤ t
  · have hkset : MeasurableSet[H k] {ω : Ω | K ω ≤ k} := by
      have hh := hstop.measurableSet_le k
      convert hh using 1
      ext ω
      simp only [Set.mem_setOf_eq, ← WithTop.coe_natCast, WithTop.coe_le_coe]
      rfl
    have hinc : H k ≤ 𝓕.rightCont t := by
      rw [hH k]
      exact (𝓕.rightCont).mono hct
    have hmain : MeasurableSet[𝓕.rightCont t] {ω : Ω | K ω ≤ k} :=
      hinc _ hkset
    convert hmain using 1
    ext ω
    simp only [Set.mem_setOf_eq, hct, and_true]
  · have hempty :
        {ω : Ω | K ω ≤ k ∧ clock k ≤ t} = (∅ : Set Ω) := by
      ext ω
      simp [hct]
    rw [hempty]
    exact @MeasurableSet.empty Ω (𝓕.rightCont t)
