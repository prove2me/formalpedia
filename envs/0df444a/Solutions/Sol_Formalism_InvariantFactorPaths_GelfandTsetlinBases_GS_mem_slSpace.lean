-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_slSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:01.18086+00:00
-- url     : https://prove2.me/submissions/c7effcbf-2d56-487b-893a-ef3a1096e4d4

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
theorem _root_.solution {P : MvPolynomial σ A} {f : MvPolynomial σ k} :
    f ∈ slSpace (k := k) P ↔ ∃ ℓ : A →ₗ[k] k, slc ℓ P = f := Iff.rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
