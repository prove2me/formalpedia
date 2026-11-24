-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resOntoKThm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:29.460274+00:00
-- url     : https://prove2.me/submissions/4f9134c4-ca6c-4b39-b6ec-7320a4011d16

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_zero_mem_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_setLast_self
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_surjective

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
theorem _root_.solution (hΩ : OmegaInj) : ResOntoKThm := by
  intro p _ K r _ LL q J M ρ e1 hr hρ hv hHP x hx
  have h0 := zero_mem_erase ρ hr hρ
  have key := restriction_surjective hΩ LL J M ρ hr hρ hv (fun Mt => by
    obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
      {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} (fun la la' hl => by
        show (((la 0 : ℤ) : WithTop ℤ) ≤ Mt) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ Mt)
        rw [hl 0 h0])
    exact ⟨P, hP⟩) (LL.deg (Fin.last K))
  rw [setLast_self] at key
  exact key x hx
end Formalism.InvariantFactorPaths.L4
