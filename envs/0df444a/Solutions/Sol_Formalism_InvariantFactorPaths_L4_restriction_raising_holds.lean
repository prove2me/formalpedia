-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restriction_raising_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:40.712247+00:00
-- url     : https://prove2.me/submissions/aa6867dd-4b84-47f0-9b79-f0c31e6b225b

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_eulL
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_zero_X_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_X_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct


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
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : ResU := by
  intro p _ K r LL c ρ a F ha
  change resL p (Fin.last K, ρ) 0 _ = Uop p LL c (univ.erase ρ) a (resL p (Fin.last K, ρ) 0 F)
  have hne : ∀ b : Fin r, b ≠ ρ → ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, ρ) :=
    fun b hb h => hb (Prod.mk.inj h).2
  rw [Uop_apply, Uop_apply, map_sub, map_sum, resL_X_mul _ _ (hne a ha), map_sub, map_smul, resL_eulL]
  congr 1
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ ρ), resL_apply, initPart_zero_X_mul, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [resL_X_mul _ _ (hne b (Finset.mem_erase.mp hb).1), resL_glAct LL K a b (Fin.last K, ρ) 0 (fun i hi =>
    ⟨fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm, fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm⟩)]
end Formalism.InvariantFactorPaths.L4
