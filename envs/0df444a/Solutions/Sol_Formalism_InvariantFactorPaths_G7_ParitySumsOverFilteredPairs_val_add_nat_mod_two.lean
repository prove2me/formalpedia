-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.val_add_nat_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:04.189386+00:00
-- url     : https://prove2.me/submissions/0ce21fa4-e0aa-46c7-b8e0-0110c0936564

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
theorem _root_.solution [NeZero ν] (x : ZMod (2 * ν)) (m : ℕ) :
    (x + (m : ZMod (2 * ν))).val % 2 = (x.val + m) % 2 := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 ν), Nat.add_mod,
    Nat.mod_mod_of_dvd _ (dvd_mul_right 2 ν), ← Nat.add_mod]
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
