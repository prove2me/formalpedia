-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.exists_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:14.255068+00:00
-- url     : https://prove2.me/submissions/1846f61b-c066-465e-8b18-f5d284096eb6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof

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
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (μ : Fin n → ℤ) : ∃ lo hi : ℤ, lo ≤ 0 ∧ 0 ≤ hi ∧ ∀ m, lo ≤ μ m ∧ μ m ≤ hi := by
  have h : ∀ m, |μ m| ≤ ∑ m, |μ m| := fun m =>
    Finset.single_le_sum (f := fun m => |μ m|) (fun i _ => abs_nonneg _) (mem_univ m)
  have h0 : 0 ≤ ∑ m, |μ m| := Finset.sum_nonneg fun i _ => abs_nonneg _
  exact ⟨-∑ m, |μ m|, ∑ m, |μ m|, by omega, h0, fun m => abs_le.1 (h m)⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
