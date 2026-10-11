-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:53.30198+00:00
-- url     : https://prove2.me/submissions/53a6a8a3-a3c7-4aa6-bd34-6c9ec5287d24

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq
import Mathlib
import Definitions.Def_ChapterWeylSl2
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
theorem solution {R : Sl2Rep V} (v : V) :
    R.cas v = 2 • (R.E (R.F v) + R.F (R.E v)) + R.H (R.H v) := rfl
