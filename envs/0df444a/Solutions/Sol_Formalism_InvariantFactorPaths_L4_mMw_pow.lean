-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mMw_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:15:59.499426+00:00
-- url     : https://prove2.me/submissions/7c489471-6d88-4a33-a508-3658da676dcc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pol_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtSpC_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hWC_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_pow
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ) (he : e ≤ LL.deg (Fin.last K))
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ MMw p LL J M ρ w ↔
      h ∈ MMw p (setLast LL (LL.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) := by
  simp only [MMw, Y, Submodule.mem_inf, Submodule.mem_iInf, pol_pow LL ρ e he, yCond_pow LL hv ρ e,
    hWC_pow LL hv ρ e (LL.deg (Fin.last K) - e), wtSpC_pow LL hv ρ e (LL.deg (Fin.last K) - e),
    yCond_setLast, shiftLastLetterThresholds]
end Formalism.InvariantFactorPaths.L4
