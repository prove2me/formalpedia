-- Prove2me | solution 1 for BookProof.TensorPerm.inner_purePow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:14.049006+00:00
-- url     : https://prove2.me/submissions/ed2d60f1-2726-4b8b-891b-fd293687162f

-- Generated from ChapterTensorPermutation.lean — solution of BookProof.TensorPerm.inner_purePow
import Mathlib
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorPerm




open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

variable (E : BookProof.TensorCore.IPSpace)

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (n : ℕ) (f g : Fin n → E.carrier),
    (inner ℂ (purePow E n f) (purePow E n g) : ℂ) = ∏ i, inner ℂ (f i) (g i) := by

  intro n
  induction n with
  | zero =>
      intro f g
      change (inner ℂ (1 : ℂ) (1 : ℂ) : ℂ) = _
      simp
  | succ n ih =>
      intro f g
      rw [purePow_succ, purePow_succ, TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]
      rfl
