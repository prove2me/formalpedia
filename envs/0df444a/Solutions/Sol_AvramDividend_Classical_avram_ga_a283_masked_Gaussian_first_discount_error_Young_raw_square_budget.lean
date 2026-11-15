-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a283_masked_Gaussian_first_discount_error_Young_raw_square_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:18:30.194416+00:00
-- url     : https://prove2.me/submissions/26297edf-af6d-43c3-888b-22f5f3ffdd15

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)] (r : ℕ → Ω → ℝ)
    (η Q L : ℝ) (hη : 0 < η)
    (hQ : 0 ≤ Q) (hL : 0 ≤ L) (ω : Ω) :
    (∑ i ∈ S, if A i ω then Q*L*|r i ω| else 0) ≤
      η*(∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
        (S.card : ℝ)*(Q*L)^2/(4*η) := by
  classical
  let c := (Q*L)^2/(4*η)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hEach (i : ℕ) :
      (if A i ω then Q*L*|r i ω| else 0) ≤
      η*(if A i ω then (r i ω)^2 else 0)+c := by
    by_cases hAi : A i ω
    · simp only [if_pos hAi]
      exact avram_ga_a281_discount_raw_first_increment_Young_square_budget
        η Q L (r i ω) hη hQ hL
    · simp only [if_neg hAi, mul_zero, zero_add]
      exact hc
  calc
    (∑ i ∈ S, if A i ω then Q*L*|r i ω| else 0) ≤
        ∑ i ∈ S, (η*(if A i ω then (r i ω)^2 else 0)+c) :=
      Finset.sum_le_sum (fun i hi => hEach i)
    _ = η*(∑ i ∈ S, if A i ω then (r i ω)^2 else 0) +
          (S.card : ℝ)*(Q*L)^2/(4*η) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul,c]
      ring
