-- Prove2me | solution 1 for CommitOpen.Benign.lemma_2_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:49:42.624187+00:00
-- url     : https://prove2.me/submissions/fb51d356-605d-45b4-9f4a-3624e74a6f4f

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace X5CO

open CommitOpen.Benign Matrix

theorem rank_reducedE {ι I E : Type} [Fintype ι] [Fintype I] [Fintype E]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) :
    (reducedE (superposition b J α φE)).rank ≤ J.card := by
  classical
  set φ := superposition b J α φE
  let A : Matrix E ι ℂ := Matrix.of fun e a => φ (a, e)
  let Φ : Matrix E J ℂ := Matrix.of fun e i => φE i.1 e
  let B : Matrix J ι ℂ := Matrix.of fun i a => α i.1 * b i.1 a
  have h1 : reducedE φ = A * Aᴴ := by
    ext e e'; simp [reducedE, A, Matrix.mul_apply]
  have h2 : A = Φ * B := by
    ext e a
    simp only [A, Φ, B, φ, superposition, Matrix.of_apply, Matrix.mul_apply]
    rw [← Finset.sum_coe_sort J]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1]
  calc (A * Aᴴ).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ = (Φ * B).rank := congrArg Matrix.rank h2
    _ ≤ Φ.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card J := Matrix.rank_le_card_width _
    _ = J.card := Fintype.card_coe J

end X5CO

open CommitOpen.Benign in
theorem solution {ι I E : Type} [Fintype ι] [Fintype I] [Fintype E]
    (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) :
    maxEntropy (reducedE (superposition b J α φE)) ≤ Real.logb 2 (J.card : ℝ) := by
  have h := X5CO.rank_reducedE b J α φE
  unfold maxEntropy
  rcases Nat.eq_zero_or_pos (reducedE (superposition b J α φE)).rank with h0 | hp
  · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]
    rcases Nat.eq_zero_or_pos J.card with hJ | hJ
    · simp [hJ]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hJ)
  · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hp) (by exact_mod_cast h)
