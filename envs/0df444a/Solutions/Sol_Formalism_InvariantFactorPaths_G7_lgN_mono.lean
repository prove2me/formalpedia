-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.lgN_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:01:53.024804+00:00
-- url     : https://prove2.me/submissions/0798770c-db90-4d02-b571-0a412165d318

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
theorem _root_.solution (p : ℕ) {x y : ℕ} (h : x ≤ y) : lgN p x ≤ lgN p y := by
  unfold lgN
  split_ifs with h1 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.succ_le_succ (Nat.log_mono_right h)
end Formalism.InvariantFactorPaths.G7
