-- Prove2me | solution 1 for BKAR.Forest.hasDerivAt_rho_interpWithFill_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:27.614526+00:00
-- url     : https://prove2.me/submissions/5ea0dd5f-5c32-49db-b4ba-cfc0797490c6

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_hasDerivAt_rho_interpWithFill_of_hasFDerivAt

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t :=
  F.hasDerivAt_rho_interpWithFill_of_hasFDerivAt u hρ.hasFDerivAt
end BKAR.Forest
