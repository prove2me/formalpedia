-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_slc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:53.561581+00:00
-- url     : https://prove2.me/submissions/89b3a990-7ece-46bd-be66-ee2370eb7d85

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable (A : Type*) [CommRing A]
variable {A}
variable {k : Type*} [Field k] [Algebra k A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (ℓ : A →ₗ[k] k) (P : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν (slc ℓ P) =
      slc ℓ (weightedHomogeneousComponent (wV isVec S) ν P) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_slc]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
