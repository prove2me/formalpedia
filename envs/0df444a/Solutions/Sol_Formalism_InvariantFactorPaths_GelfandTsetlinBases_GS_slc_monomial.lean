-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.slc_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:25.287709+00:00
-- url     : https://prove2.me/submissions/874a22a2-c39a-43b9-bdc7-08cce9f77e13

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
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (θ : A →ₗ[k] B) (e : σ →₀ ℕ) (a : A) :
    slc θ (monomial e a) = monomial e (θ a) := by
  classical
  ext e'
  simp only [coeff_slc, coeff_monomial]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
