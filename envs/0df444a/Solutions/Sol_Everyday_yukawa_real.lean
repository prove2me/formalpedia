-- Prove2me | solution 1 for Everyday.yukawa_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:40.155567+00:00
-- url     : https://prove2.me/submissions/ab784a10-4c29-44de-9b25-6037046ebc96

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open ComplexConjugate

open Everyday
/-- Matter: the Yukawa coupling plus its hermitian conjugate is real —
the "+ h.c." of the source equation makes the matter contribution to
the action a real number. -/


theorem solution {X : Type} [Fintype X] (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ) :
    (yukawaTerm ψL ψR V Φh + conj (yukawaTerm ψL ψR V Φh)).im = 0 := by
  rw [Complex.add_im, Complex.conj_im]; ring


