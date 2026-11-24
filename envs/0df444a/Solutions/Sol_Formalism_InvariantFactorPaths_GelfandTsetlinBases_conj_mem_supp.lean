-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conj_mem_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:28.299375+00:00
-- url     : https://prove2.me/submissions/c5d85b40-be53-4abd-9b0f-513bc6c2f3d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_sharp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_tw_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sharp_sharp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sharp_bij
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_part_ne_zero

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
variable {ι ζ : Type*} {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    j ∈ (conjAct (RingHom.id L) isVec S g gi last G).coeff.support ↔
      ∃ e ∈ (sharpHom isVec S gi g G).support, wExp isVec S last e = j := by
  conv_lhs => rw [← sharp_sharp isVec S h G]
  rw [conjAct_sharp isVec S h', Finsupp.mem_support_iff, tw_coeff, ← part_ne_zero]
  exact (map_ne_zero_iff _ (sharp_bij isVec S h h').1)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
