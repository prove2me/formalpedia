-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eW_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.652287+00:00
-- url     : https://prove2.me/submissions/e76cc47d-347e-4333-ad76-b10203794e18

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_ne
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (a a' : Fin r) (haa : a ≠ a') : ∀ (i : ℕ) (γ : Fin r → ℤ)
    (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), z ∈ WS p K γ → z ≠ 0 → (i : ℤ) ≤ γ a' → 0 ≤ γ a →
    ((eW p K a a') ^ i) z ≠ 0 := by
  intro i
  induction i with
  | zero => intro γ z _ hz0 _ _; simpa using hz0
  | succ i ih =>
    intro γ z hz hz0 h1 h2
    rw [pow_succ, Module.End.mul_apply]
    refine ih (shiftW γ a a') _ (eW_mem γ a a' z hz) (eW_ne γ a a' haa z hz hz0 (by push_cast at h1; omega) h2) ?_ ?_
    · simp only [shiftW, if_neg haa, if_true]
      push_cast at h1; omega
    · simp only [shiftW, if_neg (Ne.symm haa), if_true]
      omega
end Formalism.InvariantFactorPaths.L4
