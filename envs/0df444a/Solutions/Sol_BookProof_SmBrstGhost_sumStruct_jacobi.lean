-- Prove2me | solution 1 for BookProof.SmBrstGhost.sumStruct_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:02.180194+00:00
-- url     : https://prove2.me/submissions/4e8e509c-67b9-4a22-ab23-c8bb9c8939f8

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sumStruct_jacobi
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ}
    (h1 : ∀ a b c h : ι, ∑ e, (f1 a b e * f1 e c h + f1 b c e * f1 e a h
      + f1 c a e * f1 e b h) = 0)
    (h2 : ∀ a b c h : κ, ∑ e, (f2 a b e * f2 e c h + f2 b c e * f2 e a h
      + f2 c a e * f2 e b h) = 0)
    (a b c h : ι ⊕ κ) :
    ∑ e, (sumStruct f1 f2 a b e * sumStruct f1 f2 e c h
      + sumStruct f1 f2 b c e * sumStruct f1 f2 e a h
      + sumStruct f1 f2 c a e * sumStruct f1 f2 e b h) = 0 := by

  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases h with h | h <;>
    simp only [Fintype.sum_sum_type, sumStruct, mul_zero, zero_mul, add_zero, zero_add,
      Finset.sum_const_zero] <;>
    first | rfl | exact h1 a b c h | exact h2 a b c h
