-- Prove2me | solution 1 for BaconThesis.DFS.eq_5_16_5_19
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:02:51.763738+00:00
-- url     : https://prove2.me/submissions/40443dc8-d845-459a-a304-fb805832ad96

import Mathlib

open scoped Matrix ComplexOrder

namespace BaconThesis.DFS.SolM5_16

set_option linter.unusedSectionVars false

variable {s : Type} [Fintype s] [DecidableEq s]

lemma star_dot_mulVec (A : Matrix s s ℂ) (u v : s → ℂ) :
    star (star u ⬝ᵥ A *ᵥ v) = star v ⬝ᵥ Aᴴ *ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_vecMul, star_star]

lemma norm_sq_sum (A : Matrix s s ℂ) (j : s → ℂ) :
    star (A *ᵥ j) ⬝ᵥ (A *ᵥ j) = star j ⬝ᵥ (Aᴴ * A) *ᵥ j := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec]

lemma proj_term (A : Matrix s s ℂ) (j : s → ℂ) :
    star j ⬝ᵥ (A * Matrix.vecMulVec j (star j) * Aᴴ) *ᵥ j =
      (star j ⬝ᵥ A *ᵥ j) * star (star j ⬝ᵥ A *ᵥ j) := by
  rw [star_dot_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec,
    dotProduct_smul, op_smul_eq_mul, ← Matrix.dotProduct_mulVec]

end BaconThesis.DFS.SolM5_16

open BaconThesis.DFS.SolM5_16 in
theorem solution {s κ : Type} [Fintype s] [DecidableEq s] [Fintype κ]
    (A : κ → Matrix s s ℂ) (hA : ∑ i, (A i)ᴴ * A i = 1)
    (j : s → ℂ) (hj : star j ⬝ᵥ j = 1)
    (hinv : ∑ i, A i * Matrix.vecMulVec j (star j) * (A i)ᴴ = Matrix.vecMulVec j (star j)) :
    ∀ i, ∃ a : ℂ, A i *ᵥ j = a • j := by
  set a : κ → ℂ := fun i => star j ⬝ᵥ A i *ᵥ j with ha
  set w : κ → s → ℂ := fun i => A i *ᵥ j - a i • j with hw
  have hstar : ∀ i, star j ⬝ᵥ (A i)ᴴ *ᵥ j = star (a i) := fun i => by
    rw [ha, star_dot_mulVec]
  have hnorm : ∀ i, star (w i) ⬝ᵥ w i =
      star (A i *ᵥ j) ⬝ᵥ (A i *ᵥ j) - a i * star (a i) := by
    intro i
    have h1 : star (A i *ᵥ j) ⬝ᵥ j = star (a i) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hstar]
    have h2 : star j ⬝ᵥ (A i *ᵥ j) = a i := rfl
    simp only [hw, star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, h1, h2, hj, smul_eq_mul]
    ring
  have hsum1 : ∑ i, star (A i *ᵥ j) ⬝ᵥ (A i *ᵥ j) = 1 := by
    simp only [norm_sq_sum, ← dotProduct_sum, ← Matrix.sum_mulVec, hA, Matrix.one_mulVec, hj]
  have hsum2 : ∑ i, a i * star (a i) = 1 := by
    have := congrArg (fun M => star j ⬝ᵥ M *ᵥ j) hinv
    simp only [Matrix.sum_mulVec, dotProduct_sum, proj_term] at this
    rw [this, Matrix.vecMulVec_mulVec, hj]
    simpa using hj
  have hzero : ∑ i, star (w i) ⬝ᵥ w i = 0 := by
    simp only [hnorm, Finset.sum_sub_distrib, hsum1, hsum2, sub_self]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => dotProduct_star_self_nonneg (w i))).mp
    hzero
  intro i
  refine ⟨a i, ?_⟩
  have := dotProduct_star_self_eq_zero.mp (hall i (Finset.mem_univ i))
  exact sub_eq_zero.mp this
