-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.compL_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:04.484794+00:00
-- url     : https://prove2.me/submissions/03da6dbf-07f5-4760-86dc-fff4f89ff43f

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
theorem _root_.solution (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) (hx : x ∈ restrictSupport k {m | Pr m}) :
    compL k Pr x = x := by
  classical
  rw [mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_compL]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (hx (Finset.mem_coe.mpr (mem_support_iff.mpr (Ne.symm hc))))
end Formalism.InvariantFactorPaths.L4
