-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.parity_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:58.073481+00:00
-- url     : https://prove2.me/submissions/679c2580-4f2b-4162-8e95-1b1c3532af9f

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
theorem _root_.solution {ν : ℕ} [NeZero ν] {s s' y : ZMod (2 * ν)} (h : s' - s = 1 + 2 * y) :
    s'.val % 2 ≠ s.val % 2 := by
  rw [val_mod_two, val_mod_two]
  have hs : par ν s' = par ν s + 1 := by
    rw [show s' = s + (1 + 2 * y) by rw [← h]; ring, map_add, par_odd]
  rw [hs]
  generalize par ν s = a
  revert a
  decide
end Formalism.InvariantFactorPaths.G7.ValuationParity
