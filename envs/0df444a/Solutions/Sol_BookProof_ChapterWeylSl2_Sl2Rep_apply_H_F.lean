-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:41.638343+00:00
-- url     : https://prove2.me/submissions/b74883ed-f942-404d-828d-e4fc0706e90a

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_hf_prime
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
theorem solution (v : V) : R.H (R.F v) = R.F (R.H v) - 2 • R.F v := by

  have h := congrArg (fun T : Module.End ℂ V => T v) (hf_prime (R := R))
  simpa [Module.End.mul_apply] using h
