-- Prove2me | solution 1 for BKAR.Forest.hasDerivAt_rho_interpWithFill_of_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:31.150125+00:00
-- url     : https://prove2.me/submissions/3d94a1b3-0f58-4720-8290-cc8361b58386

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill
import Theorems.Thm_BKAR_Forest_apply_activeDirection_eq_activeEdgePartialSum

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    HasDerivAt (fun s : ℝ => ρ (F.interpWithFill u s))
      (F.activeEdgePartialSum u ρ t) t := by
  change HasDerivAt (ρ ∘ fun s : ℝ => F.interpWithFill u s)
    (F.activeEdgePartialSum u ρ t) t
  rw [← F.apply_activeDirection_eq_activeEdgePartialSum u hρ]
  exact hρ.comp_hasDerivAt t (F.hasDerivAt_interpWithFill u t)
end BKAR.Forest
