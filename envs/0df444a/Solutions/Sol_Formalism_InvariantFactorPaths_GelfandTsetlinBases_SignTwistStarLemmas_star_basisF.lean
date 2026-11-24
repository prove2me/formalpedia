-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.star_basisF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:47.638662+00:00
-- url     : https://prove2.me/submissions/5614734f-9293-4291-a58e-4e3cf27ba91a

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
theorem _root_.solution (I : Finset (Fin n)) :
    star (basisF I : Form R n) = ((-1 : R) ^ epsN Iᶜ) • basisF Iᶜ := by
  funext J
  simp only [star, basisF, Pi.smul_apply, smul_eq_mul]
  by_cases h : J = Iᶜ
  · subst h; simp
  · have : ¬ Jᶜ = I := fun h' => h (by rw [← h', compl_compl])
    simp [h, this]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
