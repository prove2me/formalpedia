-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:06.690738+00:00
-- url     : https://prove2.me/submissions/add671d8-061a-4909-bc71-05a6126a21d7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_C

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
theorem _root_.solution {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (G : MvPolynomial (LVar ι ζ n) k) :
    conjAct φ isVec S g gi last G = conjAct (RingHom.id L) isVec S g gi last (map φ G) := by
  suffices hh : conjAct (ζ := ζ) φ isVec S g gi last =
      (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp (map φ) from by
    rw [hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [conjAct_C]
  · intro x
    simp [conjAct]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
