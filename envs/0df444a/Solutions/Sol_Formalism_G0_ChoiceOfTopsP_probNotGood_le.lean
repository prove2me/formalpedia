-- Prove2me | solution 1 for Formalism.G0.ChoiceOfTopsP.probNotGood_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:22.630933+00:00
-- url     : https://prove2.me/submissions/56d8a368-592b-4065-aa04-d9834901ff35

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTops
import Theorems.Thm_Formalism_G0_ChoiceOfTopsP_not_good
import Theorems.Thm_Formalism_G0_ChoiceOfTopsP_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.ChoiceOfTopsP
namespace Formalism.G0.ChoiceOfTopsP
theorem _root_.solution (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    probNotGood n δ L₂ K r N₁ G ≤
      condProb n δ (fun T => ¬ CondA n T L₂ K) +
      condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) +
      condProb n δ (fun T => ¬ CondC n T G) +
      condProb n δ (fun T => T.card < N₁) := by
  classical
  unfold probNotGood condProb
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T _
  have hw : 0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
    mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)
  refine term_le _ _ _ _ _ _ hw ?_
  rintro ⟨h0T, hg⟩
  rcases not_good hg with h | h | h | h
  · exact Or.inl ⟨h0T, h⟩
  · exact Or.inr (Or.inl ⟨h0T, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0T, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0T, h⟩))
end Formalism.G0.ChoiceOfTopsP
