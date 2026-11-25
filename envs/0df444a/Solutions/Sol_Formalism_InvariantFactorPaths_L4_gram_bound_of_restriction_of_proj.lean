-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.gram_bound_of_restriction_of_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:06.810283+00:00
-- url     : https://prove2.me/submissions/99287512-dcc3-4fd7-bd04-0fe587280894

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resOntoK_of_resSat
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_saturation_at_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_projAtOf_of
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_graded_bot_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_graded_piece_bound_holds
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
theorem _root_.solution (hX : ProjX) : GramBoundOfRestriction := by
  intro p _ K r _ LLw q J M ρ e1 κ hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 3) * e1) e1 κ
      (projAtOf_of hX p K r LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSat _ J _ ρ (hS e he)))
      (saturation_at_holds p K r LLw J M ρ w e e1 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 3) * e1 + 2 * e1 = (K + 5) * e1 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp
end Formalism.InvariantFactorPaths.L4
