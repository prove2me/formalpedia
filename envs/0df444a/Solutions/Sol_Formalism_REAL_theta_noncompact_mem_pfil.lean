-- Prove2me | solution 1 for Formalism.REAL.theta_noncompact_mem_pfil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:52.493432+00:00
-- url     : https://prove2.me/submissions/f64e17d4-8eb1-414c-ba78-c87c17c5b818

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_word_action_mem_pfil
import Theorems.Thm_Formalism_REAL_symmetrization_apply
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff
import Theorems.Thm_Formalism_REAL_reverse_of_fn_noncompact

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (j : ℕ) (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) :
    thetaA E j F ∈ pfil ε E u j := by
  rw [symmetrization_apply (E := E) (F := F)]
  refine sum_mem (fun α _ => ?_)
  have hα := (mem_noncompact_arr_iff ε E u F).mp hF α
  by_cases h : ∀ i, ε (α i).1 ≠ ε (α i).2
  · rw [if_pos h] at hα
    exact word_action_mem_pfil ε E u j _ (by simp) (reverse_of_fn_noncompact ε α h) _ hα
  · rw [if_neg h, Submodule.mem_bot] at hα
    rw [hα, map_zero]
    exact Submodule.zero_mem _
end Formalism.REAL
