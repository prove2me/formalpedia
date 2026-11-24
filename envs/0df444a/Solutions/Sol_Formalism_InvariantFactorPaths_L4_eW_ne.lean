-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eW_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.917658+00:00
-- url     : https://prove2.me/submissions/93afd542-17ac-4012-946c-e385c783e77a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_XDXD
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_WS_eig
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (γ : Fin r → ℤ) (a a' : Fin r) (haa : a ≠ a') (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hz : z ∈ WS p K γ) (hz0 : z ≠ 0) (h1 : 0 < γ a') (h2 : 0 ≤ γ a) : eW p K a a' z ≠ 0 := by
  intro h0
  have hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, a') := fun h => haa (Prod.mk.inj h).2
  have h := XDXD _ _ hne z _ _ (WS_eig γ z hz a) (WS_eig γ z hz a')
  rw [eW_apply] at h0
  rw [h0, map_zero, mul_zero] at h
  rcases smul_eq_zero.mp h.symm with h3 | h3
  · have h4 : ((γ a' * (γ a + 1) : ℤ) : ℚ_[p]) = 0 := by push_cast; exact h3
    have h5 := Int.cast_eq_zero.mp h4
    rcases mul_eq_zero.mp h5 with h6 | h6 <;> omega
  · exact hz0 h3
end Formalism.InvariantFactorPaths.L4
