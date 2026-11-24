-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pow_mul_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:50.525633+00:00
-- url     : https://prove2.me/submissions/25d80e02-5897-45a0-8472-bb31c2605619

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : Fin r) (x g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : glAct p LL j 0 c (glAct p LL j 0 c x) = 0) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (x * g) = x * ((glAct p LL j 0 c) ^ (k + 1)) g +
      ((k + 1 : ℕ) : ℚ_[p]) • (glAct p LL j 0 c x * ((glAct p LL j 0 c) ^ k) g) := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, pow_zero, glAct_mul, Nat.cast_one, one_smul, Module.End.one_apply]
    exact add_comm _ _
  | succ k ih =>
    have e1 : ∀ n y, glAct p LL j 0 c (((glAct p LL j 0 c) ^ n) y) = ((glAct p LL j 0 c) ^ (n + 1)) y := by
      intro n y
      rw [pow_succ', Module.End.mul_apply]
    rw [← e1 (k + 1), ih, map_add, map_smul, glAct_mul, glAct_mul, hx, zero_mul, zero_add, e1, e1]
    push_cast
    simp only [add_smul, one_smul]
    abel
end Formalism.InvariantFactorPaths.L4
