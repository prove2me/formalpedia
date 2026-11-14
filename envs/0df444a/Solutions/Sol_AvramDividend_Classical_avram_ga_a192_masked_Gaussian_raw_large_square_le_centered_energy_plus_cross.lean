-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:09.729196+00:00
-- url     : https://prove2.me/submissions/92e6de83-7e00-40f1-8b0b-40d249454e36

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Large raw squared physical Gaussian source cells are pointwise dominated
by the centred quadratic energy and absolute raw-centred cross. -/
theorem solution
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (Z : ℕ → Ω → ℝ) (d η : ℝ) (ω : Ω) :
    let Tail : ℝ := ∑ i ∈ S, if A i ω then
      (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) else 0
    let Energy : ℝ := ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0
    let Cross : ℝ := ∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0
    0 ≤ Tail ∧ Tail ≤ Energy + Cross := by
  classical
  intro Tail Energy Cross
  constructor
  · dsimp [Tail]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  · dsimp [Tail,Energy,Cross]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases ha : A i ω
    · simp only [if_pos ha]
      by_cases ht : η ≤ |Z i ω + d|
      · simp only [if_pos ht]
        have hh := le_abs_self ((Z i ω + d)^2 - (Z i ω)^2)
        linarith
      · simp only [if_neg ht]
        positivity
    · simp only [if_neg ha]
      norm_num
