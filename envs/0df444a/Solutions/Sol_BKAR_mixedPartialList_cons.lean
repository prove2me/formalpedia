-- Prove2me | solution 1 for BKAR.mixedPartialList_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:55.574263+00:00
-- url     : https://prove2.me/submissions/4b5b4ac0-2e50-4637-9290-02d4b5a1f261

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (e :: es) ρ = partialDeriv e (mixedPartialList es ρ) :=
  rfl
end BKAR
