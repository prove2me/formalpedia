-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.derivative_keeps_space_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:14.8458+00:00
-- url     : https://prove2.me/submissions/81e4ad61-9980-4529-b0be-2b19e571c80e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_zero_mem_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_last_letter_mem

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
theorem _root_.solution : DKeepsX := by
  intro p _ K r _ LL q J M ρ a e1 o hr hρ hv hHP ha x hx
  have h0 := zero_mem_erase ρ hr hρ
  refine pderiv_last_letter_mem LL J M ρ a o hr hρ hv (fun Mt => ?_) ha x hx
  obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
    {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ Mt) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ Mt)
      rw [hl 0 h0])
  exact ⟨P, hP⟩
end Formalism.InvariantFactorPaths.L4
