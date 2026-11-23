-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.WS_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:13.956807+00:00
-- url     : https://prove2.me/submissions/087f3009-1360-4292-8ba5-b544a8707ce4

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_of_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_WD_cw

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
theorem _root_.solution (γ : Fin r → ℤ) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hz : z ∈ WS p K γ) (c : Fin r) :
    X (Fin.last K, c) * pderiv (Fin.last K, c) z = ((γ c : ℤ) : ℚ_[p]) • z := by
  have h := WD_cw γ c z
  rwa [show cw p K γ z = z from compL_of_mem _ z hz] at h
end Formalism.InvariantFactorPaths.L4
