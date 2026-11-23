-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.phi_parity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:33.097711+00:00
-- url     : https://prove2.me/submissions/439ec86b-f6c5-4bc4-8018-d926177f50ff

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_val_add_nat_mod_two

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
theorem _root_.solution [NeZero ν] (φ : PhiI ν r0 r1 E) :
    (pairSecond φ).val % 2 = ((pairFirst φ).val + 1) % 2 := by
  have hν : 1 ≤ 2 * ν := by have := NeZero.ne ν; omega
  have e : pairSecond φ = pairFirst φ +
      (((1 + 2 * φ.2.1.val + 2 * (φ.2.2.1.val * (2 * ν - 1))) : ℕ) : ZMod (2 * ν)) := by
    unfold pairFirst pairSecond
    have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
    push_cast [Nat.cast_sub hν] at h0 ⊢
    linear_combination (-(2 * (φ.2.2.1.val : ZMod (2 * ν)))) * h0
  rw [e, val_add_nat_mod_two]
  omega
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
