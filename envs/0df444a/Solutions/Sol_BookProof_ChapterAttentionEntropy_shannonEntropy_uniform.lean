-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.shannonEntropy_uniform
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:20:37.831978+00:00
-- url     : https://prove2.me/submissions/1362772d-580e-4bb2-a2b1-e1e652af0544

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_uniform
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

theorem solution (hm : 0 < m) :
    shannonEntropy (fun _ : Fin m => (1 : ℝ) / m) = Real.log m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [shannonEntropy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div, Real.log_inv]
  field_simp

#print axioms solution

