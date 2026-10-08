-- Prove2me | solution 1 for BookProof.ChapterAttentionCapacity.distScore_margin_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:30.355117+00:00
-- url     : https://prove2.me/submissions/d88e3ee4-cf5c-4cdd-ab19-fc3fad0de521

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.distScore_margin_of_separated
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution {k : Fin m → EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) :
    ∀ l, l ≠ i → distScore (k i) k l + r ^ 2 ≤ distScore (k i) k i := by
  intro l hl
  have h := hsep i l (Ne.symm hl)
  have hn := norm_nonneg (k i - k l)
  simp only [distScore, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), neg_zero]
  nlinarith

#print axioms solution

