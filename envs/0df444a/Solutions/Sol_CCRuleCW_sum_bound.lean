-- Prove2me | solution 1 for CCRuleCW.sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:36:40.968968+00:00
-- url     : https://prove2.me/submissions/616d9642-02cd-4ef8-be6c-bef6d8f07a95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
namespace CCRuleCW
theorem _root_.solution {α β : Type*} (l : List α) (S : Set β) (w : β → ℝ) (φ : α → β → ℝ)
    (h : ∀ p ∈ l, ∃ C, ∀ g ∈ S, φ p g ≤ C * w g) :
    ∃ C, ∀ g ∈ S, (l.map (fun p => φ p g)).sum ≤ C * w g := by
  induction l with
  | nil => exact ⟨0, fun g _ => by simp⟩
  | cons a l ih =>
    obtain ⟨C₁, h₁⟩ := h a (by simp)
    obtain ⟨C₂, h₂⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨C₁ + C₂, fun g hg => ?_⟩
    simp only [List.map_cons, List.sum_cons]
    have e1 := h₁ g hg
    have e2 := h₂ g hg
    nlinarith
end CCRuleCW
