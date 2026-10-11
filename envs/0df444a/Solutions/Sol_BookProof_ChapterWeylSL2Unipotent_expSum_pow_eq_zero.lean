-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:41:00.504292+00:00
-- url     : https://prove2.me/submissions/56d7c2b3-ef49-4db7-a5c7-42a99245c665

-- Generated from ChapterWeylSL2Unipotent.lean — solution of BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero
import Mathlib
import Definitions.Def_ChapterWeylSL2Unipotent
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterWeylSL2Group
open BookProof.ChapterWeylSL2Unipotent




open BookProof.ChapterWeylSl2 BookProof.ChapterWeylSL2Group
open Polynomial

universe u

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {A : Module.End ℂ V} {N m : ℕ} (hnil : A ^ N = 0) (hNm : N ≤ m) :
    A ^ m = 0 := by

  rw [show m = N + (m - N) by omega, pow_add, hnil, zero_mul]
