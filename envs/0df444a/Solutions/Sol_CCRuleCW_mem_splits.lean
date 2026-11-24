-- Prove2me | solution 1 for CCRuleCW.mem_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:03.667099+00:00
-- url     : https://prove2.me/submissions/af07fc3e-e172-4ade-9a90-82a205585c26

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
theorem _root_.solution {α : Type*} : ∀ (l : List α) (p : List α × List α), p ∈ splits l →
    p.1.Sublist l ∧ p.2.Sublist l
  | [], p, h => by
      simp only [splits, List.mem_singleton] at h
      subst h
      exact ⟨List.Sublist.slnil, List.Sublist.slnil⟩
  | x :: xs, p, h => by
      simp only [splits, List.mem_append, List.mem_map] at h
      rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have := solution xs q hq
        exact ⟨this.1.cons_cons x, this.2.cons x⟩
      · have := solution xs q hq
        exact ⟨this.1.cons x, this.2.cons_cons x⟩
end CCRuleCW
