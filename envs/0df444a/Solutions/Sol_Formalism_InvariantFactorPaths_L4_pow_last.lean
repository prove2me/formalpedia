-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pow_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:49.849669+00:00
-- url     : https://prove2.me/submissions/aa47d2c0-8b1c-460f-a076-1c24f27dac82

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (X (Fin.last K, c) * h) =
      X (Fin.last K, c) * ((glAct p LL j 0 c) ^ (k + 1)) h +
        ((k + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, (0 : Fin r)) * ((glAct p LL j 0 c) ^ k) h) := by
  have h1 : ∀ y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 c (X (Fin.last K, c) * y) =
        X (Fin.last K, (0 : Fin r)) * y + X (Fin.last K, c) * glAct p LL j 0 c y := by
    intro y
    rw [glAct_mul, last_X p LL j hj hv, if_pos rfl]
  have h2 : ∀ z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 c (X (Fin.last K, (0 : Fin r)) * z) =
        X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 c z := by
    intro z
    rw [glAct_mul, last_X p LL j hj hv, if_neg hc, zero_mul, zero_add]
  have hpow : ∀ (n : ℕ) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      ((glAct p LL j 0 c) ^ (n + 1)) y = glAct p LL j 0 c (((glAct p LL j 0 c) ^ n) y) := by
    intro n y
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero =>
    rw [hpow 0, pow_zero, Module.End.one_apply, Module.End.one_apply, h1]
    simp only [zero_add, Nat.cast_one, one_smul]
    abel
  | succ k ih =>
    rw [hpow (k + 1), ih, map_add, map_smul, h1, h2, ← hpow k, ← hpow (k + 1)]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
end Formalism.InvariantFactorPaths.L4
