-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sharp_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:14.440518+00:00
-- url     : https://prove2.me/submissions/74817903-e9bb-41f8-a638-318ae15ae7a6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sharp_sharp

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
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) :
    Function.Bijective (sharpHom (ζ := ζ) isVec S g gi) :=
  ⟨Function.LeftInverse.injective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h'),
   Function.RightInverse.surjective (g := sharpHom (ζ := ζ) isVec S gi g) (sharp_sharp isVec S h)⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
