-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_iN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:24.007158+00:00
-- url     : https://prove2.me/submissions/3e053ca6-1d36-4a29-b3e8-4d9ee9bbe0be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_sum_filter_fst

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
theorem _root_.solution [NeZero ν] (β : KapI ν r1 E →₀ ℕ) (A : Finset (ZMod (2 * ν))) :
    ∑ s ∈ A, ∑ e' ∈ range E, iN β s e' =
      ∑ k ∈ univ.filter (fun k : KapI ν r1 E => k.1 ∈ A), β k := by
  rw [sum_filter_fst A (fun k => β k)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_range (fun e' => iN β s e'), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp [iN, e.isLt]
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
