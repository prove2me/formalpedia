-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoC_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:35.261617+00:00
-- url     : https://prove2.me/submissions/b5b2432d-591e-447d-b797-a15d8c183b7e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_map_of_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_stable


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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c c x ∈ IsoC p LL j Cs la := by
  intro x hx
  by_cases hc : c ∈ Cs
  · exact isoC_stable LL j Cs la c hc c hc x hx
  · refine isoC_map_of_comm LL j Cs (glAct p LL j c c) (fun c' hc' d' hd' y => ?_) la x hx
    have h := glAct_comm (p := p) LL j c c c' d' y
    have h1 : ¬ c = c' := fun h => hc (h ▸ hc')
    have h2 : ¬ d' = c := fun h => hc (h ▸ hd')
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
    exact h
end Formalism.InvariantFactorPaths.PW
