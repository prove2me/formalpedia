-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:21:57.608992+00:00
-- url     : https://prove2.me/submissions/ed95f204-646b-4c83-9062-e80abb815f49

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxOrder BookProof.ChapterCoherentOverlap
variable {n : ℕ}

theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) : shannonEntropy p ≤ Real.log m := by
  have hm : 0 < m := by
    by_contra hcon
    have : m = 0 := by omega
    subst this
    simp at hsum
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ j ∈ Finset.univ,
      -(p j * Real.log (p j)) - p j * Real.log m ≤ 1 / m - p j := by
    intro j _
    rcases eq_or_lt_of_le (hp0 j) with h | h
    · simp [← h]
    · have hx : 0 < 1 / ((m : ℝ) * p j) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hx
      have hrw : Real.log (1 / ((m : ℝ) * p j))
          = -(Real.log m + Real.log (p j)) := by
        rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hmR) (ne_of_gt h)]
      rw [hrw] at hlog
      have hmul : p j * (-(Real.log m + Real.log (p j)))
          ≤ p j * (1 / ((m : ℝ) * p j) - 1) := by
        exact mul_le_mul_of_nonneg_left hlog h.le
      have hsimp : p j * (1 / ((m : ℝ) * p j) - 1) = 1 / m - p j := by
        field_simp
      rw [hsimp] at hmul
      nlinarith [hmul]
  have hsum' := Finset.sum_le_sum hterm
  have hleft : ∑ j, (-(p j * Real.log (p j)) - p j * Real.log m)
      = shannonEntropy p - Real.log m := by
    rw [Finset.sum_sub_distrib, shannonEntropy, ← Finset.sum_neg_distrib,
      ← Finset.sum_mul, hsum, one_mul]
  have hright : ∑ j : Fin m, ((1 : ℝ) / m - p j) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div, div_self (ne_of_gt hmR), sub_self]
  rw [hleft, hright] at hsum'
  linarith

#print axioms solution

