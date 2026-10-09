-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:32:56.705153+00:00
-- url     : https://prove2.me/submissions/f27d813e-a16c-4dfb-9a10-055b9d72655d

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 < p j)
    (v : Fin m → E) :
    outputVariance p v = 0 ↔ ∀ j, v j = observableExpectation p v := by

  constructor
  · intro h j
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ p i * ‖v i - observableExpectation p v‖ ^ 2 :=
      fun i _ => mul_nonneg (hp0 i).le (sq_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h j (Finset.mem_univ j)
    have hn : ‖v j - observableExpectation p v‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hzero with hp | hn
      · exact absurd hp (hp0 j).ne'
      · exact hn
    have : ‖v j - observableExpectation p v‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hn
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · intro h
    rw [outputVariance]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h j]
    simp
