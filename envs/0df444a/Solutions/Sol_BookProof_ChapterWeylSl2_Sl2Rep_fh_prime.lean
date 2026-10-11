-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.fh_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:36.250928+00:00
-- url     : https://prove2.me/submissions/a7514aa3-4b6d-48e1-ad87-f08fbcd97c38

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.fh'
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}

set_option maxHeartbeats 1000000 in
theorem solution : R.F * R.H - R.H * R.F = 2 • R.F := by

  rw [← neg_sub (R.H * R.F), R.hf, neg_neg]
