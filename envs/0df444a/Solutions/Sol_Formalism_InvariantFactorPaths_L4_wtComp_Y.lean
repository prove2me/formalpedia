-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtComp_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:24:20.59486+00:00
-- url     : https://prove2.me/submissions/365736de-ace8-4c04-b5c6-3000d9498f93

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_keep_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cartan_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_wcomp_mem
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_min


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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (w : Fin r → ℤ) :
    ∀ h ∈ Y p LL J M, wtComp p LL N w h ∈ Y p LL J M := by
  intro h hh
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  refine Submodule.mem_inf.mpr ⟨wtComp_keep_supp LL N w _ h hhP, ?_⟩
  rw [Submodule.mem_iInf]
  intro k
  have hk := hhY k
  rw [ycond_min] at hk ⊢
  exact wcomp_mem LL N _ (fun c x hx => cartan_ycond LL _ N (min_le_right _ _) (M k) c x hx) w h hk
end Formalism.InvariantFactorPaths.L4
