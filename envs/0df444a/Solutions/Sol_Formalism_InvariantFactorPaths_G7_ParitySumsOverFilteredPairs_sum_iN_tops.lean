-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN_tops
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:36.687406+00:00
-- url     : https://prove2.me/submissions/f5b8b952-9d03-477c-861e-82b39c67fc9a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_iN

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
theorem _root_.solution [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (TT : Finset (ZMod (2 * ν)))
    (h2 : ∀ k, β k ≠ 0 → k.1 ∈ TT) :
    ∑ s ∈ TT, ∑ e' ∈ range E, iN β s e' = ∑ k, β k := by
  rw [sum_iN β TT]
  exact Finset.sum_filter_of_ne (fun k _ hk => h2 k hk)
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
