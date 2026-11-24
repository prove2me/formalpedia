-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.EC_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.267463+00:00
-- url     : https://prove2.me/submissions/55d79812-8776-42e4-85f0-75359666119d

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_eq_of_dependsOn
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_sum_le_prob
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_eq
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_card
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_even_card
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_dep_EC

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
theorem _root_.solution {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {r u s c : ℕ} (hc : 1 ≤ c)
    (hU : cell r u s c ⊆ U) :
    (if Odd c then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) ≤
      P U δ (EC r u s c) := by
  classical
  rw [prob_eq_of_dependsOn δ hU (dep_EC r u s c)]
  split_ifs with hodd
  · have := sum_le_prob (S := cell r u s c) (A := EC r u s c) h0 h1 {∅} (by
      intro t ht
      rw [mem_singleton] at ht
      subst ht
      exact ⟨empty_subset _, fun _ => empty_inter _,
        fun he => absurd hodd (Nat.not_odd_iff_even.2 he)⟩)
    simpa [cell_card hc] using this
  · have hev : Even c := Nat.not_odd_iff_even.1 hodd
    have := sum_le_prob (S := cell r u s c) (A := EC r u s c) h0 h1
      (((cell r u s c).filter Even).image (fun x => {x})) (by
      intro t ht
      rw [mem_image] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [mem_filter] at hx
      exact ⟨singleton_subset_iff.2 hx.1, fun ho => absurd ho hodd,
        fun _ => ⟨x, inter_eq_left.2 (singleton_subset_iff.2 hx.1), hx.2⟩⟩)
    rw [sum_image (fun x _ y _ h => singleton_injective h)] at this
    simp only [card_singleton, pow_one, cell_card hc, sum_const, nsmul_eq_mul] at this
    refine le_trans ?_ this
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg h0 (pow_nonneg (by linarith) _))
    have := even_card (s * ((6 * r + 1) * u) + (c - 1) * u) u
    rw [← cell_eq hc] at this
    exact_mod_cast this
end Formalism.G0.TopsChoiceProbabilityLemmas
