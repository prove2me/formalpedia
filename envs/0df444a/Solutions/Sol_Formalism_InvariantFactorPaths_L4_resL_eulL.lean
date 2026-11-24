-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resL_eulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:46.479363+00:00
-- url     : https://prove2.me/submissions/46a0a5ca-04ad-47bd-aeaa-5563a251aa30

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_GM_ProjS_coeff_eulL
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_apply
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
theorem _root_.solution {σ : Type} {s : ℕ} (t : Fin s → σ) (v : σ) (e : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    resL p v e (ProjS.eulL t x) = ProjS.eulL t (resL p v e x) := by
  ext m
  rw [resL_apply, resL_apply, coeff_initPart, ProjS.coeff_eulL, ProjS.coeff_eulL, coeff_initPart]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.L4
