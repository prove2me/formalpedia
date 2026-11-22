-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.coeff_compL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:43:57.459064+00:00
-- url     : https://prove2.me/submissions/2ac8095b-bd35-4b35-8342-327d27f2f1a6

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP


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
variable {k σ : Type} [Field k]
open Classical
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (compL k Pr x) = if Pr m then coeff m x else 0 := coeff_compP Pr x m
end Formalism.InvariantFactorPaths.L4
