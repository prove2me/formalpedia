-- Prove2me | solution 1 for Formalism.REAL.mem_noncompact_arr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:55.146464+00:00
-- url     : https://prove2.me/submissions/9c5d6489-e0f5-4bb1-adb2-2bc99e5910c5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_fin_one_fun_eq_const_apply_zero
import Theorems.Thm_Formalism_REAL_mem_noncompact_arr_iff_general

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
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {F : Arr V n 1}
    (h1 : ∀ a b, ε a ≠ ε b → F (fun _ => (a, b)) ∈ kSpan ε E u)
    (h2 : ∀ a b, ε a = ε b → F (fun _ => (a, b)) = 0) : F ∈ arrV0 ε E u 1 := by
  rw [mem_noncompact_arr_iff_general]
  intro α
  rw [fin_one_fun_eq_const_apply_zero α]
  by_cases h : ε (α 0).1 = ε (α 0).2
  · rw [if_neg (fun h' => h' 0 h), Submodule.mem_bot]; exact h2 _ _ h
  · rw [if_pos (fun _ => h)]; exact h1 _ _ h
end Formalism.REAL
