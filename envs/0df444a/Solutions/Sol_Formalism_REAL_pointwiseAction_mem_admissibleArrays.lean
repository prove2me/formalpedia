-- Prove2me | solution 1 for Formalism.REAL.pointwiseAction_mem_admissibleArrays
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:02.290128+00:00
-- url     : https://prove2.me/submissions/bdce9fed-39bb-498d-ae4a-2ee49285c220

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_pointwiseAction_apply
import Theorems.Thm_Formalism_REAL_mem_admissibleArrays
import Theorems.Thm_Formalism_REAL_compactSpan_invariant
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
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) {a b : Fin n} (hab : ε a = ε b) :
    ptE E a b F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [pointwiseAction_apply]
  by_cases hα : ∀ k, ε (α k).1 ≠ ε (α k).2
  · rw [if_pos hα]
    exact compactSpan_invariant ε E u a b hab _ (admissibleArrays_apply_mem hF α)
  · rw [if_neg hα, Submodule.mem_bot, admissibleArrays_apply_eq_zero hF α hα, map_zero]
end Formalism.REAL
