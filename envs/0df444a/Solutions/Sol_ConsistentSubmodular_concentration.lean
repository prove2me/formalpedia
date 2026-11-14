-- Prove2me | solution 1 for ConsistentSubmodular.concentration
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:45.728398+00:00
-- url     : https://prove2.me/submissions/3deff9f7-a62d-4aac-913c-46f7a52372d0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_lower_tail_le
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_card_chernoff

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace Tails

/-- **Lemma B.7** (concentration), for a random subset of `{0, ..., d - 1}`. -/
theorem concentration : ConcentrationGoal := by
  refine ⟨fun d q G c a hq hG hmono hsub hc hcap => ?_, fun d q κ η hq hmass hη hη1 => ?_⟩
  · dsimp only
    intro ha haμ
    have hEq : independentExpectation Finset.univ q G = sampleExpectation Finset.univ q G := rfl
    rw [hEq] at haμ ⊢
    have hp : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ q i ∧ q i ≤ 1 := fun i _ => hq i
    exact sampleExpectation_lower_tail_le Finset.univ q hp G hmono hsub hc hcap (ha.trans haμ)
      (by linarith [hG ∅]) ha.le
  · exact sampleExpectation_card_chernoff Finset.univ q (fun i _ => hq i) hmass hη hη1

end Tails

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : ConcentrationGoal :=
  Tails.concentration

end
