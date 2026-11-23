-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.compL_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:04.860122+00:00
-- url     : https://prove2.me/submissions/e322e807-a2b5-473d-9425-285649a4bc5d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_compL

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
theorem _root_.solution (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) :
    compL k Pr x ∈ restrictSupport k {m | Pr m} := by
  classical
  rw [mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_compL] at hm
  split_ifs at hm with h
  · exact h
  · exact absurd rfl hm
end Formalism.InvariantFactorPaths.L4
