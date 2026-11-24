-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.one_le_dAof_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.533139+00:00
-- url     : https://prove2.me/submissions/3b295502-9aa2-4cb3-b422-d1e8b0be5f65

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB

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
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution {p : ℕ} (hp : 0 < p) (φ : PhiI ν r0 r1 E) :
    1 ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by
  unfold dAof
  rw [Finsupp.add_apply, Finsupp.single_eq_same]
  exact le_trans (Nat.one_le_pow (2 * φ.2.2.1.val) p hp) (Nat.le_add_left _ _)
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
