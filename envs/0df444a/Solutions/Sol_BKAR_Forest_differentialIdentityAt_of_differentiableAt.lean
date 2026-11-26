-- Prove2me | solution 1 for BKAR.Forest.differentialIdentityAt_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:39.494568+00:00
-- url     : https://prove2.me/submissions/c4845971-a459-4802-b91f-54f42b0b5d7b

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_differentialIdentityAt_of_hasFDerivAt

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    F.ActiveEdgeDerivIdentityAt u ρ t :=
  F.differentialIdentityAt_of_hasFDerivAt u hρ.hasFDerivAt
end BKAR.Forest
