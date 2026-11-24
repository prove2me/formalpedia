-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lam_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:21.372035+00:00
-- url     : https://prove2.me/submissions/a014867e-0947-4294-9f49-874846fbe9a3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_max_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (G H : MvPolynomial (LVar ι ζ n) k) :
    lam1S isVec S (G + H) ≤ max (lam1S isVec S G) (lam1S isVec S H) := by
  simp only [lam1S, map_add]; exact lp_max_add _ _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
