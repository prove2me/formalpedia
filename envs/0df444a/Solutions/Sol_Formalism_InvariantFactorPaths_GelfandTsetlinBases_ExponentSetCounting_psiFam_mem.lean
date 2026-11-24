-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.psiFam_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:19:51.827674+00:00
-- url     : https://prove2.me/submissions/72d7b9c1-c3c1-46a8-91df-67e065850ece

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductDegrees


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
theorem _root_.solution (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
