-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:40.053981+00:00
-- url     : https://prove2.me/submissions/616a8bcf-e095-45b5-9784-903fbab516ff

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_he_prime
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
theorem solution (v : V) : R.H (R.E v) = R.E (R.H v) + 2 • R.E v := by

  have h := congrArg (fun T : Module.End ℂ V => T v) (he_prime (R := R))
  simpa [Module.End.mul_apply] using h
