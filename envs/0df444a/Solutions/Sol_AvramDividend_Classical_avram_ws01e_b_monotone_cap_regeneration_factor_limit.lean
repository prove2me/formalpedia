-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_monotone_cap_regeneration_factor_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:09:47.761985+00:00
-- url     : https://prove2.me/submissions/2df476fd-251b-4218-ba75-6b7817b3dd87

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (E : ℕ → Set α) (hE : Monotone E)
    (B : Set α) (c : ℝ≥0∞)
    (hFactor : ∀ n : ℕ, μ (E n ∩ B) = ν (E n) * c) :
    μ ((⋃ n : ℕ, E n) ∩ B) = ν (⋃ n : ℕ, E n) * c := by
  have hInter : Monotone (fun n : ℕ => E n ∩ B) := by
    intro m n hmn x hx
    exact ⟨hE hmn hx.1, hx.2⟩
  have hSet : ((⋃ n : ℕ, E n) ∩ B) =
      ⋃ n : ℕ, E n ∩ B := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    aesop
  calc
    μ ((⋃ n : ℕ, E n) ∩ B) =
      μ (⋃ n : ℕ, E n ∩ B) := by rw [hSet]
    _ = ⨆ n : ℕ, μ (E n ∩ B) := hInter.measure_iUnion
    _ = ⨆ n : ℕ, ν (E n) * c := by simp_rw [hFactor]
    _ = (⨆ n : ℕ, ν (E n)) * c :=
      (ENNReal.iSup_mul (fun n => ν (E n)) c).symm
    _ = ν (⋃ n : ℕ, E n) * c := by rw [hE.measure_iUnion]
