-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Uop_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:32.878483+00:00
-- url     : https://prove2.me/submissions/65eebea1-cba4-44b7-91a1-213eea3009c0

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eulW_eq
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
theorem _root_.solution (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL c Cs a F =
      X (Fin.last K, a) * (((c : ℤ) : ℚ_[p]) • F - ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F) -
        ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by
  simp only [Uop, Wm, eulW_eq, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sum_apply]
end Formalism.InvariantFactorPaths.L4
