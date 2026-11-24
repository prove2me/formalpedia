-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.isLeast_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:58.817897+00:00
-- url     : https://prove2.me/submissions/c40675a1-6e31-4cbf-a587-96ee9f12a7e0

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
theorem _root_.solution {n : ℕ} [NeZero n] (s s' : ZMod n) (h : 1 ≤ (s' - s).val) :
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} (s' - s).val := by
  refine ⟨⟨h, by rw [ZMod.natCast_zmod_val]; ring⟩, ?_⟩
  rintro e ⟨_, he⟩
  have he' : ((e : ℕ) : ZMod n) = s' - s := by rw [← he]; ring
  rw [← he', ZMod.val_natCast]
  exact Nat.mod_le _ _
end Formalism.InvariantFactorPaths.G7.ValuationParity
