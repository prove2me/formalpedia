-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:30.401889+00:00
-- url     : https://prove2.me/submissions/f550ee32-f705-460e-abc8-73b7c79cb324

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_apply_H_F
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_pow_succ_apply
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) :
    R.H ((R.F ^ k) w) = (lam - 2 * k) • (R.F ^ k) w := by

  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [pow_succ_apply, apply_H_F, ih, map_smul, two_nsmul]
      push_cast
      module
