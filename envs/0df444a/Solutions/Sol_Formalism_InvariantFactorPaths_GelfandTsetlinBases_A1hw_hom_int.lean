-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.hom_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:23.252859+00:00
-- url     : https://prove2.me/submissions/c1ea3524-0055-4247-a766-b15c23159f0b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
theorem _root_.solution {σ R M : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M) (z : ℤ) :
    IsWeightedHomogeneous w ((z : ℤ) : MvPolynomial σ R) 0 := by
  rw [← map_intCast (C : R →+* MvPolynomial σ R)]
  exact isWeightedHomogeneous_C w _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
