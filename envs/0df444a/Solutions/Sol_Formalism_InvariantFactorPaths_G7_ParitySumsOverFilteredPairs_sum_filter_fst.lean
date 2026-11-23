-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.sum_filter_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:04.012427+00:00
-- url     : https://prove2.me/submissions/96500f09-d057-4edf-9379-9c1566da7bd2

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
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution {A B M : Type*} [Fintype A] [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (S : Finset A) (f : A × B → M) :
    ∑ x ∈ univ.filter (fun x : A × B => x.1 ∈ S), f x = ∑ s ∈ S, ∑ y, f (s, y) := by
  have h : univ.filter (fun x : A × B => x.1 ∈ S) = S ×ˢ univ := by
    ext x
    simp
  rw [h, Finset.sum_product]
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
