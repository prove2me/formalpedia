-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.neg_one_pow_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:40.806128+00:00
-- url     : https://prove2.me/submissions/83969ae4-3e9c-4a2a-8305-2e0adcf9f296

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution {a b : ℕ} (h : Even (a + b)) : (-1 : R) ^ a = (-1) ^ b := by
  obtain ⟨c, hc⟩ := h
  rw [neg_one_pow_eq_pow_mod_two (n := a), neg_one_pow_eq_pow_mod_two (n := b)]
  congr 1
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
