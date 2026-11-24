-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.saturation_at_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:59.527553+00:00
-- url     : https://prove2.me/submissions/4b49d431-3c3a-498a-8a20-a20acdb54a01

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resOntoK_of_resSat
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grSpan_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_graded_eq_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_int_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_min_max_int_holds


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
theorem _root_.solution : SatAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 hr hρ hv he hP hE hS x hx hxI
  obtain ⟨y, hy, rfl⟩ := (grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSat _ J _ ρ hS) x).mp hx
  rw [pow_mul_int_iff] at hxI
  obtain ⟨h, hh, hres⟩ := restriction_min_max_int_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 hr hρ hv hP hE hS y hy hxI
  refine (graded_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, ?_⟩
  rw [hres, mul_smul_comm]
end Formalism.InvariantFactorPaths.L4
