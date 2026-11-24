-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_keeps_early_letters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:23.126849+00:00
-- url     : https://prove2.me/submissions/dfa8a050-dfbf-4004-9a30-1f2a5a68c5de

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ops_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_GM_FockB_mulLeftX_mem
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_split
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_mem
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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : UKeepsEarly := by
  intro p _ K r _ LL c Cs a j M hj F hF
  have hl : ∀ b : Fin r, ((Fin.last K, b) : Fin (K + 1) × Fin r) ∈ {v : Fin (K + 1) × Fin r | j ≤ (v.1 : ℕ)} := by
    intro b
    simp only [Set.mem_ofPred_eq, Fin.val_last]; exact hj
  have hX : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, X (Fin.last K, b) * x ∈ YCond p LL j M := fun b =>
    ops_ycond LL j M (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, b))) (FockB.mulLeftX_mem (hl b))
  have hD : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, pderiv (Fin.last K, b) x ∈ YCond p LL j M := fun b =>
    ops_ycond LL j M (pderiv (Fin.last K, b)).toLinearMap (FockB.pderiv_mem (hl b))
  rw [Uop_apply]
  refine Submodule.sub_mem _ (hX a _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_))
    (Submodule.sum_mem _ fun b _ => hX b _ ?_)
  · rw [ProjS.eulL_apply]
    exact Submodule.sum_mem _ fun b _ => hX b _ (hD b F hF)
  · rw [glAct_split LL j K a b, LinearMap.add_apply]
    exact Submodule.add_mem _ (ycond_glStable LL j M a b F hF)
      (ops_ycond LL j M (glRest p LL j K a b) (glRest_mem LL j K hj a b) F hF)
end Formalism.InvariantFactorPaths.L4
