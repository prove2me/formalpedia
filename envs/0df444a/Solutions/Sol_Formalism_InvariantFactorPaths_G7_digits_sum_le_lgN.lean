-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.digits_sum_le_lgN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:24.569634+00:00
-- url     : https://prove2.me/submissions/418712e8-39fc-4dac-8d25-3b09da632d8d

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
theorem _root_.solution (p m : ℕ) (hp : 1 < p) :
    (Nat.digits p m).sum ≤ (p - 1) * lgN p m := by
  have hlen : (Nat.digits p m).length = lgN p m := by
    unfold lgN
    split_ifs with h
    · simp [h]
    · exact Nat.length_digits p m hp h
  have h := List.sum_le_card_nsmul (Nat.digits p m) (p - 1)
    (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp hd))
  rw [hlen, smul_eq_mul, mul_comm] at h
  exact h
end Formalism.InvariantFactorPaths.G7
