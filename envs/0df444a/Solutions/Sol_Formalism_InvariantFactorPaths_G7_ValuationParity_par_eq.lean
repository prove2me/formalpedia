-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.par_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:58.790817+00:00
-- url     : https://prove2.me/submissions/57bf3717-7ded-45be-aead-5039f6a5884b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ValuationParity
namespace Formalism.InvariantFactorPaths.G7.ValuationParity
theorem _root_.solution {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : par ν x = ((x.val : ℕ) : ZMod 2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  show ZMod.cast x = _
  exact ZMod.cast_eq_val x
end Formalism.InvariantFactorPaths.G7.ValuationParity
