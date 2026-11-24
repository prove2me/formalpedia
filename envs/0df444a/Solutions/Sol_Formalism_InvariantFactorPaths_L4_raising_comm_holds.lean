-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_comm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:01.057808+00:00
-- url     : https://prove2.me/submissions/7d839c9b-4498-4c9a-b423-fdc4ec222592

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ_comm
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
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
theorem _root_.solution : UComm := by
  intro p _ K r LL c Cs a s t F hv hs ht
  classical
  have hlt : ((Fin.last K : Fin (K + 1)) : ℕ) < K + 1 := (Fin.last K).isLt
  have hX : ∀ (b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      glAct p LL (K + 1) s t (X (Fin.last K, b) * G) =
        (if t = b then X (Fin.last K, s) * G else 0) + X (Fin.last K, b) * glAct p LL (K + 1) s t G := by
    intro b G
    rw [glAct_mul, glAct_X, if_pos hlt, if_pos hv]
    split_ifs <;> simp
  have hc : ∀ b, glAct p LL (K + 1) s t (glAct p LL K a b F) = glAct p LL K a b (glAct p LL (K + 1) s t F) +
      ((if t = a then glAct p LL K s b F else 0) - (if b = s then glAct p LL K a t F else 0)) := by
    intro b; rw [← glAct_succ_comm]; abel
  rw [Uop_apply, Uop_apply, map_sub, map_sum, hX, map_sub, map_smul, eul_glAct]
  simp only [hX, hc, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ b ∈ Cs, (if t = b then X (Fin.last K, s) * glAct p LL K a b F else 0) =
      X (Fin.last K, s) * glAct p LL K a t F := by
    rw [Finset.sum_ite_eq, if_pos ht]
  have h2 : ∑ b ∈ Cs, X (Fin.last K, b) * (if b = s then glAct p LL K a t F else 0) =
      X (Fin.last K, s) * glAct p LL K a t F := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos hs]
  rw [h1, h2]
  split_ifs with hta
  · rw [Uop_apply]
    simp only [mul_sub]
    abel
  · simp only [mul_zero, Finset.sum_const_zero]
    abel
end Formalism.InvariantFactorPaths.L4
