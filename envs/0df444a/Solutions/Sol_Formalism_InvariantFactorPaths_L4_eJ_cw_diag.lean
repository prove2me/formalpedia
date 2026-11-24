-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eJ_cw_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:14.602805+00:00
-- url     : https://prove2.me/submissions/2ba27ee7-46d3-4f66-b722-11f156b6aa1f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftW_self
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_WD
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_WD_cw
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cartan_eigC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ


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
variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)
include hv hx
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (s : Fin r) (hs : s ∈ Cs) (γ : Fin r → ℤ) :
    glAct p LL K s s (cw p K γ x) = ((th s - γ s : ℤ) : ℚ_[p]) • cw p K γ x := by
  have h0 := cartan_eigC LL (K + 1) Cs th x (Submodule.mem_inf.mp hx).1 s hs
  rw [glAct_succ LL hv] at h0
  have h1 := congrArg (cw p K γ) h0
  rw [map_add, map_smul, cw_glAct, cw_WD, shiftW_self, WD_cw] at h1
  rw [Int.cast_sub, sub_smul, ← h1]
  abel
end Formalism.InvariantFactorPaths.L4
