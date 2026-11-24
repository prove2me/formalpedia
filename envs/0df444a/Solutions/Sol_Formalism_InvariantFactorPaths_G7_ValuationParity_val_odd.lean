-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.val_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:52.011928+00:00
-- url     : https://prove2.me/submissions/d8e0ad2e-b79c-45d8-a134-301d3ecc40ad

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_val_mod_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_par_odd

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
theorem _root_.solution {ν : ℕ} [NeZero ν] {x y : ZMod (2 * ν)} (h : x = 1 + 2 * y) : x.val % 2 = 1 := by
  rw [val_mod_two, h, par_odd]
  rfl
end Formalism.InvariantFactorPaths.G7.ValuationParity
