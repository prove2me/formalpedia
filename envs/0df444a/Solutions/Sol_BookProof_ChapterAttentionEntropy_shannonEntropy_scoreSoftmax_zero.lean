-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:22:10.231159+00:00
-- url     : https://prove2.me/submissions/5412a6aa-bec8-472f-8945-098dcc87133b

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxOrder BookProof.ChapterCoherentOverlap
variable {n : ℕ}

theorem scoreSoftmax_zero (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax 0 s j = 1 / m := by
  simp [scoreSoftmax]

theorem shannonEntropy_uniform (hm : 0 < m) :
    shannonEntropy (fun _ : Fin m => (1 : ℝ) / m) = Real.log m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [shannonEntropy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div, Real.log_inv]
  field_simp

theorem solution (s : Fin m → ℝ) (hm : 0 < m) :
    shannonEntropy (fun j => scoreSoftmax 0 s j) = Real.log m := by
  have hfun : (fun j : Fin m => scoreSoftmax 0 s j) = fun _ : Fin m => (1 : ℝ) / m :=
    funext fun j => scoreSoftmax_zero s j
  rw [hfun, shannonEntropy_uniform hm]

#print axioms solution

