-- Prove2me | solution 1 for BookProof.TensorPerm.purePow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:15.374758+00:00
-- url     : https://prove2.me/submissions/0d547e93-ac06-459d-aa5a-f5a45619286b

-- Generated from ChapterTensorPermutation.lean — solution of BookProof.TensorPerm.purePow_ne_zero
import Mathlib
import Definitions.Def_ChapterTensorPermutation
import Theorems.Thm_BookProof_TensorPerm_inner_purePow
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorPerm




open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

variable (E : BookProof.TensorCore.IPSpace)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {f : Fin n → E.carrier} (hf : ∀ i, f i ≠ 0) :
    purePow E n f ≠ 0 := by

  intro h
  have h0 : (inner ℂ (purePow E n f) (purePow E n f) : ℂ) = 0 := by rw [h, inner_zero_left]
  rw [inner_purePow] at h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
  exact (inner_self_ne_zero.mpr (hf i)) hi
