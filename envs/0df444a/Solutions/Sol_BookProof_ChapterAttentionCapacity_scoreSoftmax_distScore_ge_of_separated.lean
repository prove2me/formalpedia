-- Prove2me | solution 1 for BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:32.440378+00:00
-- url     : https://prove2.me/submissions/20326bc3-5ee5-47d4-8525-552830a74408

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution {k : Fin m → EuclideanSpace ℝ (Fin n)}
    {r beta : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) :
    1 / (1 + ((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2)))
      ≤ scoreSoftmax beta (distScore (k i) k) i := by
  classical
  have hm : 1 ≤ m := by have := i.isLt; omega
  have hi : distScore (k i) k i = 0 := by simp [distScore]
  have hmargin : ∀ l, l ≠ i → distScore (k i) k l + r ^ 2 ≤ 0 := by
    intro l hl
    have h := hsep i l (Ne.symm hl)
    have hn := norm_nonneg (k i - k l)
    dsimp [distScore]
    nlinarith
  have hterm : ∀ l ∈ (Finset.univ.erase i), Real.exp (beta * distScore (k i) k l) ≤
      Real.exp (-(beta * r ^ 2)) := by
    intro l hl
    apply Real.exp_le_exp.mpr
    have h := hmargin l (Finset.ne_of_mem_erase hl)
    nlinarith [mul_nonneg hb (show 0 ≤ -(distScore (k i) k l + r ^ 2) by linarith)]
  have hsum : (∑ l, Real.exp (beta * distScore (k i) k l)) ≤
      1 + ((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2)) := by
    have h := Finset.sum_le_sum hterm
    have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
      simp [Finset.card_erase_of_mem, Nat.cast_sub hm]
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi]
    simp only [mul_zero, Real.exp_zero]
    linarith
  have hp : 0 < ∑ l, Real.exp (beta * distScore (k i) k l) :=
    Finset.sum_pos' (fun l _ => (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ _, Real.exp_pos _⟩
  unfold scoreSoftmax
  rw [hi, mul_zero, Real.exp_zero]
  exact one_div_le_one_div_of_le hp hsum

#print axioms solution

