-- Prove2me | solution 1 for Conway99Formal.TwoSidedSchur.complementary_block_sum
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T06:11:40.763427+00:00
-- url     : https://prove2.me/submissions/282ded5a-e26f-4977-9924-7a814c0b5f34

import Definitions.Def_TwoSidedSchur
import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

namespace Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]
































section LiteralBlocks

variable {h : Type*} [Fintype h] [DecidableEq g] [DecidableEq h]





end LiteralBlocks
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

































variable {h : Type*} [Fintype h] [DecidableEq g] [DecidableEq h]

open Conway99Formal.TwoSidedSchur in
theorem solution (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) :
    firstBlock K W R + secondBlock K W R = (28 : ℝ) • 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [firstBlock, secondBlock, Matrix.fromBlocks, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply] <;>
    split_ifs <;> ring
