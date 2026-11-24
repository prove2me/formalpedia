-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.X_mul_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:16.154829+00:00
-- url     : https://prove2.me/submissions/201ed82f-8460-4096-8af5-36e88b743caa

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pol_pow
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
theorem _root_.solution (LL : Letters (K + 1)) (a : Fin r) (o : ℕ) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hG : G ∈ Pol p r (setLast LL o)) : X (Fin.last K, a) * G ∈ Pol p r (setLast LL (o + 1)) := by
  have e : setLast (setLast LL (o + 1)) ((setLast LL (o + 1)).deg (Fin.last K) - 1) = setLast LL o := by
    simp [setLast]
  have h := (pol_pow (p := p) (setLast LL (o + 1)) a 1 (by simp [setLast]) G).mpr (by rw [e]; exact hG)
  rwa [pow_one] at h
end Formalism.InvariantFactorPaths.L4
