-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dpow_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:10.697997+00:00
-- url     : https://prove2.me/submissions/d9fb34e0-f983-4d48-8379-42a18c10346d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_of_sq
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
    dpow p LL j c (k + 1) (x * g) = x * dpow p LL j c (k + 1) g + glAct p LL j 0 c x * dpow p LL j c k g := by
  simp only [dpow, LinearMap.smul_apply]
  rw [pow_mul_of_sq p LL j c x g hx k, smul_add, smul_smul, mul_smul_comm, mul_smul_comm]
  congr 2
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
end Formalism.InvariantFactorPaths.L4
