-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.prob_le_card_eq_binUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:24.658255+00:00
-- url     : https://prove2.me/submissions/165afbda-bd97-431f-998d-ba6d94a32f57

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution (S : Finset ℕ) (δ : ℝ) (N : ℕ) :
    P S δ (fun a => N ≤ a.card) = binUpper S.card δ N := by
  classical
  unfold P binUpper
  beta_reduce
  rw [show (∑ t ∈ S.powerset, _) = ∑ t ∈ S.powerset,
      (fun j => if N ≤ j then δ ^ j * (1 - δ) ^ (S.card - j) else 0) t.card from
    sum_congr rfl (fun t _ => by by_cases h : N ≤ t.card <;> simp [h])]
  rw [sum_powerset_apply_card (fun j => if N ≤ j then δ ^ j * (1 - δ) ^ (S.card - j) else 0)]
  simp only [nsmul_eq_mul, mul_ite, mul_zero]
  rw [← sum_filter]
  have hs : (range (S.card + 1)).filter (fun j => N ≤ j) = Icc N S.card := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [hs]
  apply sum_congr rfl
  intro j _
  ring
end Formalism.G0.TopsChoiceProbabilityLemmas
