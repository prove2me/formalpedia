-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:31.335354+00:00
-- url     : https://prove2.me/submissions/37973f43-1a0a-47db-b5ce-8d3a9bbe9a60

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_apply_E_F
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_pow_succ_apply
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_H_pow_F
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) (k : ℕ) :
    R.E ((R.F ^ (k + 1)) w) = ((k + 1 : ℂ) * (lam - k)) • (R.F ^ k) w := by

  induction k with
  | zero =>
      rw [pow_succ_apply, pow_zero, Module.End.one_apply, apply_E_F, hE, h, map_zero]
      push_cast
      module
  | succ k ih =>
      have hstep : R.E ((R.F ^ (k + 2)) w) = R.F (R.E ((R.F ^ (k + 1)) w))
          + R.H ((R.F ^ (k + 1)) w) := by
        rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ_apply, apply_E_F]
      rw [hstep, ih, H_pow_F h (k + 1), map_smul, ← pow_succ_apply]
      push_cast
      module
