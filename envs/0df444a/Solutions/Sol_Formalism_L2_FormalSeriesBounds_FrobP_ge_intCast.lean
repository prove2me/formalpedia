-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.ge_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:06.876845+00:00
-- url     : https://prove2.me/submissions/96ba3a91-7162-4508-bf8a-401f24394c69

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution (z : ℤ) : V.Ge 0 (z : C) := by
  have hnat : ∀ m : ℕ, (0 : WithTop ℝ) ≤ V.v (m : C) := by
    intro m
    induction m with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      push_cast
      exact le_trans (le_min ih (by rw [AddValuation.map_one])) (AddValuation.map_add _ _ _)
  unfold VF.Ge
  rw [WithTop.coe_zero]
  rcases Int.eq_nat_or_neg z with ⟨m, rfl | rfl⟩
  · simpa using hnat m
  · push_cast
    rw [AddValuation.map_neg]
    simpa using hnat m
end Formalism.L2.FormalSeriesBounds.FrobP
