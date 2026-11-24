-- Prove2me | solution 1 for Formalism.REAL.noncompact_arr_one_compact_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:08.98641+00:00
-- url     : https://prove2.me/submissions/43c8c297-e085-4592-b820-533b51d12ba7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_arr_operator_one_apply
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_values
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_one
import Theorems.Thm_Formalism_REAL_compact_span_stable_general

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} :
    KStable ε (arrE E 1) (arrV0 ε E u 1) := by
  intro c d hcd F hF
  have hval := noncompact_arr_one_values hF
  have hks := compact_span_stable_general (ε := ε) (F := E) u
  apply mem_noncompact_arr_one
  · intro a b hne
    rw [arr_operator_one_apply]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (hks c d hcd _ ((hval a b).1 hne))
    · split_ifs with h
      · subst h; exact (hval d b).1 (by rw [← hcd]; exact hne)
      · exact Submodule.zero_mem _
    · split_ifs with h
      · subst h; exact (hval a c).1 (by rw [hcd]; exact hne)
      · exact Submodule.zero_mem _
  · intro a b he
    rw [arr_operator_one_apply, (hval a b).2 he, map_zero, add_zero]
    have e1 : (if a = c then F (fun _ => (d, b)) else 0) = 0 := by
      split_ifs with h
      · subst h; exact (hval d b).2 (by rw [← hcd]; exact he)
      · rfl
    have e2 : (if b = d then F (fun _ => (a, c)) else 0) = 0 := by
      split_ifs with h
      · subst h; exact (hval a c).2 (by rw [hcd]; exact he)
      · rfl
    rw [e1, e2, sub_zero]
end Formalism.REAL
