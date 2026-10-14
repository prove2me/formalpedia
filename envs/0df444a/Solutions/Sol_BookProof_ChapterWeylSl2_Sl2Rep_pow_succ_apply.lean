-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:28.369476+00:00
-- url     : https://prove2.me/submissions/e351377f-c24d-4643-86c0-d64557fbfca3

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply
import Mathlib
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution (T : Module.End ℂ V) (k : ℕ) (v : V) :
    (T ^ (k + 1)) v = T ((T ^ k) v) := by

  rw [pow_succ']
  rfl
