-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.prob_subset_eq_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:03.713049+00:00
-- url     : https://prove2.me/submissions/8b27ea00-9dac-4f0a-aee8-58cec0fb0d54

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

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
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) :
    P U δ (fun t => S ⊆ t) = δ ^ S.card := by
  classical
  let g : ℕ → ℝ := fun i => if i ∈ S then 0 else 1 - δ
  have hprod : ∏ i ∈ U, ((fun _ => δ) i + g i) = δ ^ S.card := by
    have : ∀ i ∈ U, ((fun _ => δ) i + g i) = if i ∈ S then δ else 1 := by
      intro i _
      simp only [g]
      split_ifs <;> ring
    rw [prod_congr rfl this, prod_ite_mem, inter_eq_right.2 hS, prod_const]
  rw [← hprod, prod_add]
  unfold P
  apply sum_congr rfl
  intro t ht
  have htU : t ⊆ U := mem_powerset.1 ht
  rw [prod_const]
  by_cases hSt : S ⊆ t
  · rw [if_pos hSt]
    have : ∀ i ∈ U \ t, g i = 1 - δ := by
      intro i hi
      have hit : i ∉ S := fun h => (mem_sdiff.1 hi).2 (hSt h)
      simp only [g, if_neg hit]
    rw [prod_congr rfl this, prod_const, card_sdiff_of_subset htU]
  · rw [if_neg hSt]
    obtain ⟨i, hiS, hit⟩ := not_subset.1 hSt
    have : ∏ i ∈ U \ t, g i = 0 :=
      prod_eq_zero (mem_sdiff.2 ⟨hS hiS, hit⟩) (by simp only [g, if_pos hiS])
    rw [this, mul_zero]
end Formalism.G0.TopsConditionalProbabilityWindows
