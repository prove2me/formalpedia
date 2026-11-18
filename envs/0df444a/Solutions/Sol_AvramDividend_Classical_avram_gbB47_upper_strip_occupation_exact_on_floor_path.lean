-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB47_upper_strip_occupation_exact_on_floor_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:26:02.961203+00:00
-- url     : https://prove2.me/submissions/246a0bbb-e0c5-4452-9d87-7edaeb9ba8d8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
/-- The entire strictly pre-horizon upper-strip occupation contributes its elapsed time. -/
theorem solution (n T b : ℝ) (hT : 0 < T) (hTn : T ≤ n)
    (Y : ℝ → ℝ)
    (hY : ∀ t : ℝ, 0 < t → t < T → b < Y t)
    (hMeas : MeasurableSet {t : ℝ | t < T ∧ b < Y t}) :
    (∫ t in Ioo (0 : ℝ) n,
        if t < T ∧ b < Y t then (1 : ℝ) else 0 ∂volume) = T := by
  classical
  let S : Set ℝ := {t | t < T ∧ b < Y t}
  have hS : MeasurableSet S := hMeas
  have hSet : Ioo (0 : ℝ) n ∩ S = Ioo 0 T := by
    ext t
    constructor
    · rintro ⟨⟨ht0, _⟩, ⟨htT, _⟩⟩
      exact ⟨ht0, htT⟩
    · rintro ⟨ht0, htT⟩
      exact ⟨⟨ht0, lt_of_lt_of_le htT hTn⟩, ⟨htT, hY t ht0 htT⟩⟩
  have hPoint : ∀ t : ℝ,
      (if t < T ∧ b < Y t then (1 : ℝ) else 0) =
        S.indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t < T ∧ b < Y t
    · simp [S, Set.indicator, ht]
    · simp [S, Set.indicator, ht]
  calc
    (∫ t in Ioo (0 : ℝ) n,
        if t < T ∧ b < Y t then (1 : ℝ) else 0 ∂volume) =
      ∫ t in Ioo (0 : ℝ) n, S.indicator (fun _ => (1 : ℝ)) t ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t _
        exact hPoint t
    _ = ∫ t in Ioo (0 : ℝ) n ∩ S, (1 : ℝ) ∂volume :=
      setIntegral_indicator hS
    _ = ∫ t in Ioo (0 : ℝ) T, (1 : ℝ) ∂volume := by rw [hSet]
    _ = T := by
      rw [setIntegral_one_eq_measureReal]
      simpa only [Real.volume_real_Ioo_of_le (le_of_lt hT), sub_zero]
