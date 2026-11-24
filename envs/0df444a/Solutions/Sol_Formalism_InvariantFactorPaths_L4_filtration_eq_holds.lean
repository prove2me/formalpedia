-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.filtration_eq_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:35:23.775901+00:00
-- url     : https://prove2.me/submissions/d2cf0336-be3b-4cae-a66c-42b787754531

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_order
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_pow_div
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mMwZ_pow
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
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : FilEq := by
  intro p _ K r _ LLw q J M ρ w e hv he f
  simp only [FilE, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hZ, hS⟩
    obtain ⟨h, rfl⟩ := exists_pow_div _ e f hS
    exact ⟨h, (mMwZ_pow LLw hv J M ρ w e he h).mp hZ, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(mMwZ_pow LLw hv J M ρ w e he h).mpr hh, pow_mul_order _ e h⟩
end Formalism.InvariantFactorPaths.L4
