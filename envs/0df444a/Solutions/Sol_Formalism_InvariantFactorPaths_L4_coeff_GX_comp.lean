-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.coeff_GX_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:18.049337+00:00
-- url     : https://prove2.me/submissions/8a183673-f1b0-4cde-80fe-6783cbe75a9c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (c : ℤ) (hv : LL.vec (Fin.last K) = true) (μ : Fin (s + 1) → ℤ)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) :
    coeff m ((GX p LL c hv).comp μ x) = if wtX LL c m = μ then coeff m x else 0 :=
  coeff_compW (wtX LL c) μ x m
end Formalism.InvariantFactorPaths.L4
