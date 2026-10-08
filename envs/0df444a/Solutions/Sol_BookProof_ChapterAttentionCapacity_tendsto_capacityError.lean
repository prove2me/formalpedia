-- Prove2me | solution 1 for BookProof.ChapterAttentionCapacity.tendsto_capacityError
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:28.255014+00:00
-- url     : https://prove2.me/submissions/b6578986-11f4-44a3-9544-96264e4184e4

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.tendsto_capacityError
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

theorem solution {r C : ℝ} (hr : 0 < r) (M : ℝ) :
    Tendsto (fun b : ℝ => 2 * C * (M * Real.exp (-(b * r ^ 2)))) atTop (𝓝 0) := by
  have hp : 0 < r ^ 2 := sq_pos_of_pos hr
  have ht : Tendsto (fun b : ℝ => -(b * r ^ 2)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const hp)
  have he := Real.tendsto_exp_atBot.comp ht
  simpa using (he.const_mul M).const_mul (2 * C)

#print axioms solution

