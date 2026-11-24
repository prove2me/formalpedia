-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.compL_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:50.698236+00:00
-- url     : https://prove2.me/submissions/b00b26aa-c01d-48e1-b337-71e90da8d60a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_of_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_of_not
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_compL_add_not

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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (T : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (Pr Pr' : (σ →₀ ℕ) → Prop)
    (h1 : ∀ x ∈ restrictSupport k {m | Pr' m}, T x ∈ restrictSupport k {m | Pr m})
    (h2 : ∀ x ∈ restrictSupport k {m | ¬ Pr' m}, T x ∈ restrictSupport k {m | ¬ Pr m}) (x : MvPolynomial σ k) :
    compL k Pr (T x) = T (compL k Pr' x) := by
  conv_lhs => rw [← compL_add_not Pr' x]
  rw [map_add, map_add, compL_of_mem Pr _ (h1 _ (compL_mem Pr' x)),
    compL_of_not Pr _ (h2 _ (compL_mem (fun m => ¬ Pr' m) x)), add_zero]
end Formalism.InvariantFactorPaths.L4
