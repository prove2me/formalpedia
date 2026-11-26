-- Prove2me | solution 1 for BKAR.Forest.differentialIdentityAt_of_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:37.277548+00:00
-- url     : https://prove2.me/submissions/fcec4c29-2c6c-466a-93b6-def77bdcbccc

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
    F.ActiveEdgeDerivIdentityAt u ρ t := by
  rw [ActiveEdgeDerivIdentityAt, activeEdgePartialSum]
  calc
    deriv (fun s : ℝ => ρ (F.interpWithFill u s)) t =
        ρ' F.activeDirection := by
          exact (hρ.comp_hasDerivAt t (F.hasDerivAt_interpWithFill u t)).deriv
    _ = F.activeEdgePartialSum u ρ t :=
          F.apply_activeDirection_eq_activeEdgePartialSum u hρ
end BKAR.Forest
