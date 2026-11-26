-- Prove2me | solution 1 for BKAR.mixedPartialList_cons_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:57.640407+00:00
-- url     : https://prove2.me/submissions/b9b42456-2c2b-4d57-aa93-16c8f2eb7384

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    mixedPartialList (e :: es) ρ x =
      partialDeriv e (mixedPartialList es ρ) x :=
  rfl
end BKAR
