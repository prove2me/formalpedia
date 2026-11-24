-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.map_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:43.384357+00:00
-- url     : https://prove2.me/submissions/436fc7b8-25c2-4bd3-82ba-5895d6241060

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_exists_cols
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_psi_eq_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_map_pathWord


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
theorem _root_.solution {k L : Type} [CommRing k] [CommRing L] (φ : k →+* L) {n N : ℕ} {isVec : ℕ → Bool}
    {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    MvPolynomial.map φ (psiPath k isVec μ N I) = psiPath L isVec μ N I := by
  obtain ⟨F, hF⟩ := exists_cols hp
  rw [psi_eq_prod k hF hI, psi_eq_prod L hF hI, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [A1hw.map_pathWord]
  simp only [map_X]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
