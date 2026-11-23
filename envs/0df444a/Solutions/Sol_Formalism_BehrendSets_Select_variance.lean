-- Prove2me | solution 1 for Formalism.BehrendSets.Select.variance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:25.788821+00:00
-- url     : https://prove2.me/submissions/84d224ae-424f-48b6-8bc5-06154ca27873

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
import Theorems.Thm_Formalism_BehrendSets_Select_moments

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Select
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Select
theorem _root_.solution (X : Finset α) (δ : ℝ) :
    ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 = δ * X.card * (1 - δ) := by
  obtain ⟨h0, h1, h2⟩ := moments X δ
  have e : ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 =
      ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
        - 2 * (δ * X.card) * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
        + (δ * X.card) ^ 2 * ∑ T ∈ X.powerset, wt X δ T * 1 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [e, h0, h1, h2]
  ring
end Formalism.BehrendSets.Select
