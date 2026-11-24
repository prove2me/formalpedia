-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.polLatData_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:17.096003+00:00
-- url     : https://prove2.me/submissions/2f77c85c-a52b-4a97-b148-48d845531fd3

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_intPol_zpClosed
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_intPol_whc
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_fd
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_finW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divided_integral_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hB : LatBasisPol) {p : ℕ} [Fact p.Prime] {N r n : ℕ} (LL L2 : Letters N) (j : ℕ)
    (e : Fin n ↪o Fin r) :
    LatData p (GAe p LL j e) (Pol p r L2) (IntPol p (Fin N × Fin r)).toAddSubgroup L2.total where
  stable := GAe_pol_stable LL L2 j e
  fd := pol_fd L2
  finW := GAe_pol_finW LL L2 j e
  bound := GAe_pol_bound LL L2 j e
  closed := intPol_zpClosed _
  div := fun a b hab k x hx =>
    divided_integral_holds p N r LL j (e a) (e b) (fun h => hab (e.injective h)) k x hx
  graded := fun μ x hx => intPol_whc _ μ x hx
  basis := fun U hU => by
    have := pol_fd (p := p) (r := r) L2
    exact hB p _ U (Submodule.finiteDimensional_of_le hU)
end Formalism.InvariantFactorPaths.PW
