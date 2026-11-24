-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.yCond_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:32.196115+00:00
-- url     : https://prove2.me/submissions/7c4135ca-51fe-41d5-94f9-5d56db66dacf

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_early_letters_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mul_last_letter_holds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e j : ℕ) (M : WithTop ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ YCond p LL j M ↔
      h ∈ YCond p LL j (if K + 1 ≤ j then M + ((-(e : ℤ) : ℤ) : WithTop ℤ) else M) := by
  by_cases hj : K + 1 ≤ j
  · rw [if_pos hj]
    induction e generalizing M with
    | zero => simp
    | succ e ih =>
      rw [pow_succ', mul_assoc, mul_last_letter_holds p K r LL j M ρ _ hj hv, ih, add_assoc, ← WithTop.coe_add]
      have : (-1 : ℤ) + -(e : ℤ) = -((e + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]
  · rw [if_neg hj]
    induction e with
    | zero => simp
    | succ e ih => rw [pow_succ', mul_assoc, mul_early_letters_holds p K r LL j M ρ _ (by omega), ih]
end Formalism.InvariantFactorPaths.L4
