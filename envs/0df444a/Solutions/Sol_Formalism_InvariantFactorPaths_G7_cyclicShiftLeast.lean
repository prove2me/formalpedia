-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.cyclicShiftLeast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.729365+00:00
-- url     : https://prove2.me/submissions/0a7cf924-5c0b-4666-afff-2909c28abb81

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith

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
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : ChargeLemma := by
  intro n s s' a a' d haa h hd
  have hmem : a - a' ∈ {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} := by
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub haa.le]
    linear_combination h
  exact (hd.2 hmem).trans (Nat.sub_le _ _)
end Formalism.InvariantFactorPaths.G7
