-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.hom_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:56.476295+00:00
-- url     : https://prove2.me/submissions/716063c6-078b-4423-b17c-12813f9602b8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight

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
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {σ R : Type*} [CommRing R] (w : σ → ℕ) (z : ℤ) :
    IsWeightedHomogeneous w ((z : ℤ) : MvPolynomial σ R) 0 := by
  rw [← map_intCast (C : R →+* MvPolynomial σ R)]
  exact isWeightedHomogeneous_C w _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
