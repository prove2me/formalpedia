-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.val_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:38.502903+00:00
-- url     : https://prove2.me/submissions/117544a5-a55f-471b-8875-5440d5856a46

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_par_eq

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
theorem _root_.solution {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : x.val % 2 = (par ν x).val := by
  rw [par_eq, ZMod.val_natCast]
end Formalism.InvariantFactorPaths.G7.ValuationParity
