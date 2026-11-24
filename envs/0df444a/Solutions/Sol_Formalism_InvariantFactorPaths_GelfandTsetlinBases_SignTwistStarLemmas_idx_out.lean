-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.idx_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:55:29.858154+00:00
-- url     : https://prove2.me/submissions/036d375e-17c1-458a-a034-709e868f16c4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_colHeight_lo
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_colHeight_hi

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
theorem _root_.solution {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) {c : ℤ} (hc : c ∉ Finset.Ioc lo hi) : I c = ∅ := by
  rw [← Finset.card_eq_zero, hI c]
  rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  rcases hc with hc | hc
  · rw [if_neg (by omega), colHeight_lo (fun m => (hb m).1) hc]; simp
  · rw [if_pos (by omega), colHeight_hi (fun m => (hb m).2) hc]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
