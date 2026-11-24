-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.loss_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:36.326915+00:00
-- url     : https://prove2.me/submissions/c440f2cf-b230-42d0-bdb2-3fa2fbcc0a81

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : HLoss := by
  intro C C' r f b hb
  have hb0 : 0 < b := by linarith
  rw [← pow_mul]
  have e : ∀ N : ℕ, b ^ N = Real.exp ((N : ℝ) * Real.log b) := by
    intro N; rw [Real.exp_nat_mul, Real.exp_log hb0]
  rw [e, Real.exp_le_exp]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hb)
  have hr : r ^ 4 ≤ (2 * r + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have : C * (2 * r + 2) ^ 2 * f * (C' * r ^ 4) ≤ C * C' * (2 * r + 2) ^ 6 * f := by
    calc C * (2 * r + 2) ^ 2 * f * (C' * r ^ 4) ≤ C * (2 * r + 2) ^ 2 * f * (C' * (2 * r + 2) ^ 4) := by gcongr
      _ = C * C' * (2 * r + 2) ^ 6 * f := by ring
  exact_mod_cast this
end Formalism.HermitianLatticeCounting.P
