-- Prove2me | solution 1 for BookProof.ChapterA.conjFixed_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:27:29.344467+00:00
-- url     : https://prove2.me/submissions/2f012814-d543-40cf-8993-396e2b3c1750

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.conjFixed_ne_bot
import Mathlib
import Definitions.Def_ChapterA1f
import Theorems.Thm_BookProof_ChapterA_conjugation_avg_fixed
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) :
    conjFixed θ ≠ ⊥ := by

  rw [Submodule.ne_bot_iff]
  by_contra h
  push_neg at h
  have hneg : ∀ x : V, θ x = -x := by
    intro x
    have hfix : ((2⁻¹ : ℂ) • (x + θ x)) ∈ conjFixed θ := by
      rw [mem_conjFixed]; exact conjugation_avg_fixed θ hθ x
    have hzero := h _ hfix
    have hx : x + θ x = 0 := by
      have h2 : ((2 : ℂ)) • ((2⁻¹ : ℂ) • (x + θ x)) = 0 := by rw [hzero]; simp
      rw [smul_smul] at h2; norm_num at h2; exact h2
    linear_combination (norm := module) hx
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  have e1 : θ ((Complex.I) • x) = (Complex.I) • x := by rw [θ.map_smulₛₗ]; simp [hneg]
  have e2 : θ ((Complex.I) • x) = -((Complex.I) • x) := hneg _
  rw [e1] at e2
  have hz : Complex.I • x = 0 := by
    rw [eq_neg_iff_add_eq_zero] at e2
    have h2 : (2 : ℂ) • (Complex.I • x) = 0 := by rw [two_smul]; exact e2
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  rcases smul_eq_zero.mp hz with h | h
  · simp [Complex.I_ne_zero] at h
  · exact hx0 h
