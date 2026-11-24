-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.brk_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:22.12837+00:00
-- url     : https://prove2.me/submissions/74b0c55d-8804-457e-8e07-7febd4517cf8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_minorF_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isIndex_can
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_isIndex_can


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    brk g gi (μ N) I =
      ∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (canIdx (μ N) c) (I c) := by
  unfold brk
  refine finprod_eq_prod_of_mulSupport_subset _ fun c hc => ?_
  by_contra hn
  apply hc
  show minorF (if 1 ≤ c then g else gi.transpose) (canIdx (μ N) c) (I c) = 1
  rw [(hF c hn).2 I hI, (hF c hn).2 _ (A1hw.isIndex_can _)]
  exact minorF_empty _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
