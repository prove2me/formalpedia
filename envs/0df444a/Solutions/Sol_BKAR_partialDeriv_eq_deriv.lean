-- Prove2me | solution 1 for BKAR.partialDeriv_eq_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:15:06.537013+00:00
-- url     : https://prove2.me/submissions/8d980000-37c5-4a17-9838-a7dcc0cd638a

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    partialDeriv e ρ x =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e) :=
  rfl
end BKAR
