-- Prove2me | solution 1 for BKAR.mixedPartialList_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:25.634194+00:00
-- url     : https://prove2.me/submissions/a837bfd0-5722-4135-9bd6-d47b233421de

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (es₁ es₂ : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (es₁ ++ es₂) ρ =
      mixedPartialList es₁ (mixedPartialList es₂ ρ) := by
  induction es₁ with
  | nil =>
      rfl
  | cons e es ih =>
      change partialDeriv e (mixedPartialList (es ++ es₂) ρ) =
        partialDeriv e (mixedPartialList es (mixedPartialList es₂ ρ))
      rw [ih]
end BKAR
