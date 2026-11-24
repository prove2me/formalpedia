-- Prove2me | solution 1 for Formalism.REAL.factorAction_mem_admissibleArrays
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:00.692973+00:00
-- url     : https://prove2.me/submissions/228c1a1d-a272-47d7-a2bf-88122f4b2e38

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_mem_admissibleArrays
import Theorems.Thm_Formalism_REAL_admissibleArrays_apply_mem
import Theorems.Thm_Formalism_REAL_admissibleArrays_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (i : Fin j) {a b : Fin n} (hab : ε a = ε b) :
    factorAction i a b F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [factorAction_apply]
  by_cases hα : ∀ k, ε (α k).1 ≠ ε (α k).2
  · rw [if_pos hα]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact admissibleArrays_apply_mem hF _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact admissibleArrays_apply_mem hF _
      · exact Submodule.zero_mem _
  · rw [if_neg hα, Submodule.mem_bot]
    push_neg at hα
    obtain ⟨k, hk⟩ := hα
    have t1 : (if (α i).1 = a then F (Function.update α i (b, (α i).2)) else 0) = 0 := by
      split_ifs with h1
      · refine admissibleArrays_apply_eq_zero hF _ fun hall => ?_
        have hk' := hall k
        by_cases hki : k = i
        · rw [hki] at hk hk'
          simp at hk'
          exact hk' (by rw [← hab, ← h1, hk])
        · simp [Function.update_apply, hki] at hk'
          exact hk' hk
      · rfl
    have t2 : (if (α i).2 = b then F (Function.update α i ((α i).1, a)) else 0) = 0 := by
      split_ifs with h2
      · refine admissibleArrays_apply_eq_zero hF _ fun hall => ?_
        have hk' := hall k
        by_cases hki : k = i
        · rw [hki] at hk hk'
          simp at hk'
          exact hk' (by rw [hk, h2, hab])
        · simp [Function.update_apply, hki] at hk'
          exact hk' hk
      · rfl
    rw [t1, t2, sub_zero]
end Formalism.REAL
