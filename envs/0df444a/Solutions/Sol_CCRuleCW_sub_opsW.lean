-- Prove2me | solution 1 for CCRuleCW.sub_opsW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:22.931472+00:00
-- url     : https://prove2.me/submissions/ff6f5aeb-5fb1-43bc-8516-81be5e24c1f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_apO_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_nil
attribute [local simp] CCRuleCW.apO_cons

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (u v : List (B.Mat k r)) (l : List (Bool × B.Mat k r)) (h : l.Sublist (opsW u v)) :
    ∃ u' v', l = opsW u' v' ∧ (∀ X ∈ u', X ∈ u) ∧ (∀ X ∈ v', X ∈ v) := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 h
  obtain ⟨a, ha, rfl⟩ := List.sublist_map_iff.1 h₁
  obtain ⟨b, hb, rfl⟩ := List.sublist_map_iff.1 h₂
  refine ⟨b.reverse, a.reverse, by simp [opsW], fun X hX => ?_, fun X hX => ?_⟩
  · exact List.mem_reverse.1 (hb.subset (List.mem_reverse.1 hX))
  · exact List.mem_reverse.1 (ha.subset (List.mem_reverse.1 hX))
end CCRuleCW
