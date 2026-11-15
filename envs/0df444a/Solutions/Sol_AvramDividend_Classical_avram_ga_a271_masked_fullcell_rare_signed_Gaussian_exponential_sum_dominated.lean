-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:21:38.228687+00:00
-- url     : https://prove2.me/submissions/58ac7296-08af-4955-bb72-3f393d9e0d89

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (r : ℕ → Ω → ℝ) (theta delta : ℝ)
    (hθ : 0 ≤ theta) (hδ : 0 < delta) (ω : Ω) :
    (∑ i ∈ S,
      if A i ω ∧ delta ≤ |r i ω| then Real.exp (theta*r i ω) else 0) ≤
    (∑ i ∈ S,
      if A i ω ∧ delta ≤ r i ω then Real.exp (theta*r i ω) else 0) +
      (1/delta^2) * (∑ i ∈ S,
        if A i ω ∧ delta ≤ |r i ω| then (r i ω)^2 else 0) := by
  have hCell (i : ℕ) :
      (if A i ω ∧ delta ≤ |r i ω| then
        Real.exp (theta * r i ω) else 0) ≤
      (if A i ω ∧ delta ≤ r i ω then
        Real.exp (theta * r i ω) else 0) +
        (1 / delta^2) *
          (if A i ω ∧ delta ≤ |r i ω| then (r i ω)^2 else 0) := by
    by_cases ha : A i ω
    · by_cases hl : delta ≤ |r i ω|
      · have h := avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
          theta delta (r i ω) hθ hδ hl
        by_cases hp : delta ≤ r i ω
        · have h1 : A i ω ∧ delta ≤ |r i ω| := ⟨ha, hl⟩
          have h2 : A i ω ∧ delta ≤ r i ω := ⟨ha, hp⟩
          simp only [if_pos h1, if_pos h2]
          exact le_add_of_nonneg_right (by positivity)
        · have h1 : A i ω ∧ delta ≤ |r i ω| := ⟨ha, hl⟩
          have h2 : ¬ (A i ω ∧ delta ≤ r i ω) :=
            fun hh => hp hh.2
          simp only [if_neg hp] at h
          have h3 : (r i ω)^2 / delta^2 =
              (1 / delta^2) * (r i ω)^2 := by ring
          rw [h3] at h
          simpa only [if_pos h1, if_neg h2, zero_add] using h
      · have hp : ¬ delta ≤ r i ω := by
          intro hc
          exact hl (le_trans hc (le_abs_self _))
        simp [ha, hl, hp]
    · simp [ha]
  calc
    _ ≤ ∑ i ∈ S,
      ((if A i ω ∧ delta ≤ r i ω then Real.exp (theta * r i ω) else 0) +
        (1 / delta^2) *
          (if A i ω ∧ delta ≤ |r i ω| then (r i ω)^2 else 0)) :=
            Finset.sum_le_sum (fun i _ => hCell i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
