-- Prove2me | solution 1 for BookProof.ChapterDutchBook.represents_isProb_coherent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:10.612466+00:00
-- url     : https://prove2.me/submissions/4cb5ff5d-ddc9-4fbb-9120-20c9cd60739b

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.represents_isProb_coherent
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype Ω] {Pr : Finset Ω → ℝ} {p : Ω → ℝ}
    (hp : IsProb p) (hrep : Represents Pr p) : Coherent Pr := by

  rintro ⟨m, A, s, hlt⟩
  have hbet : ∀ i, ∑ ω, p ω * betIndicator (A i) ω = Pr (A i) := by
    intro i
    rw [hrep (A i)]
    simp only [betIndicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hE : ∑ ω, p ω * payoff Pr A s ω = 0 := by
    have hrw : ∀ ω, p ω * payoff Pr A s ω
        = ∑ i, s i * (p ω * betIndicator (A i) ω - p ω * Pr (A i)) := by
      intro ω; rw [payoff, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simp_rw [hrw]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum]
    have hz : ∑ ω, (p ω * betIndicator (A i) ω - p ω * Pr (A i)) = 0 := by
      rw [Finset.sum_sub_distrib, hbet i, ← Finset.sum_mul, hp.2, one_mul, sub_self]
    rw [hz, mul_zero]
  have hpos : ∃ ω, 0 < p ω := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ ω, p ω = 0 := fun ω => le_antisymm (hcon ω) (hp.1 ω)
    have hsum : ∑ ω, p ω = 0 := by simp [hz]
    rw [hp.2] at hsum; exact one_ne_zero hsum
  obtain ⟨ω0, hω0⟩ := hpos
  have hElt : ∑ ω, p ω * payoff Pr A s ω < ∑ _ω : Ω, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro ω _; exact mul_nonpos_iff.mpr (Or.inl ⟨hp.1 ω, (hlt ω).le⟩)
    · exact ⟨ω0, Finset.mem_univ _, mul_neg_of_pos_of_neg hω0 (hlt ω0)⟩
  rw [Finset.sum_const_zero, hE] at hElt
  exact lt_irrefl 0 hElt
