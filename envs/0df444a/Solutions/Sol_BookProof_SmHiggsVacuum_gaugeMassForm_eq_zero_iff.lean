-- Prove2me | solution 1 for BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:00.77289+00:00
-- url     : https://prove2.me/submissions/313fb9d2-ea3b-4309-b93a-01ff203f0e00

-- Generated from ChapterSmHiggsVacuum.lean — solution of BookProof.SmHiggsVacuum.gaugeMassForm_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum




open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (X : Fin 3 → Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) :
    gaugeMassForm X u = 0 ↔ ∀ i, (X i).mulVec u = 0 := by

  constructor
  · intro h i
    have hsum : ∑ i : Fin 3, ∑ a : Fin 4, ((X i).mulVec u a) ^ 2 = 0 := by
      have h2 : (1 / 2 : ℝ) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h2
      · exact h'
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        ∑ a : Fin 4, ((X j).mulVec u a) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum
      exact fun j _ => Finset.sum_nonneg fun a _ => sq_nonneg _
    have hi := hzero i (Finset.mem_univ i)
    have ha : ∀ a ∈ (Finset.univ : Finset (Fin 4)), ((X i).mulVec u a) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hi
      exact fun a _ => sq_nonneg _
    funext a
    have := ha a (Finset.mem_univ a)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    have hrow : ∀ i : Fin 3, ∑ a : Fin 4, ((X i).mulVec u a) ^ 2 = 0 := by
      intro i
      simp [h i]
    simp only [gaugeMassForm]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i]
    simp
