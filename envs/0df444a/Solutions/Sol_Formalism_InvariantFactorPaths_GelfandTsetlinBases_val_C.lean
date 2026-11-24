-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.val_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:13.053317+00:00
-- url     : https://prove2.me/submissions/f75ec103-a73f-4470-b3e2-360dc0974853

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_supp_C
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genAct_C

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
theorem _root_.solution {c : k} (hc : c ≠ 0) : valS (ζ := ζ) (n := n) isVec S (C c) = 0 := by
  rw [valS, genAct_C, lp_supp_C]
  · rfl
  · simpa using hc
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
