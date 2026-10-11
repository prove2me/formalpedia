-- Prove2me | solution 1 for BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:07.27678+00:00
-- url     : https://prove2.me/submissions/68964beb-680d-4a23-9b8a-062a716a0a28

-- Generated from ChapterSoftmaxMaxEntropy.lean — solution of BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) :
    shannonEntropy p ≤ crossEntropy p q := by

  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      -(p j * Real.log (p j)) + p j * Real.log (q j) ≤ q j - p j := by
    intro j _
    rcases eq_or_lt_of_le (hp0 j) with h | h
    · rw [← h]
      simpa using (hq0 j).le
    · have hratio : 0 < q j / p j := div_pos (hq0 j) h
      have hlog := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div (ne_of_gt (hq0 j)) (ne_of_gt h)] at hlog
      have hmul : p j * (Real.log (q j) - Real.log (p j))
          ≤ p j * (q j / p j - 1) := mul_le_mul_of_nonneg_left hlog h.le
      have hsimp : p j * (q j / p j - 1) = q j - p j := by field_simp
      rw [hsimp] at hmul
      nlinarith [hmul]
  have hsum := Finset.sum_le_sum hterm
  have hleft : ∑ j, (-(p j * Real.log (p j)) + p j * Real.log (q j))
      = shannonEntropy p - crossEntropy p q := by
    rw [Finset.sum_add_distrib, shannonEntropy, crossEntropy, ← Finset.sum_neg_distrib]
    ring
  have hright : ∑ j, (q j - p j) = (∑ j, q j) - 1 := by
    rw [Finset.sum_sub_distrib, hpsum]
  rw [hleft, hright] at hsum
  linarith
