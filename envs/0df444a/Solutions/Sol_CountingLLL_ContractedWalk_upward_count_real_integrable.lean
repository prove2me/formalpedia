-- Prove2me | solution 1 for CountingLLL.ContractedWalk.upward_count_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:06:06.473173+00:00
-- url     : https://prove2.me/submissions/80e1c32f-178a-47f1-b3a8-1bb70f2cb0a4

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem up_le_changes (ω : Tape) (i : ℕ) : (upwardCount ω i : ℝ≥0∞) ≤ changes ω i := by
  classical
  unfold upwardCount changes
  push_cast
  apply le_trans _ (ENNReal.sum_le_tsum (s := Finset.range (stopTime ω i)) (f := fun t => if level ω i t = 0 then 0 else 1))
  apply Finset.sum_le_sum
  intro t ht
  split_ifs <;> simp_all

theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) (i : ℕ) :
    Integrable (fun ω : Tape => (upwardCount ω i : ℝ)) (tapeLaw (ENNReal.ofReal θ)) := by
  have hm : Measurable (fun ω : Tape => (upwardCount ω i : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (upward_count_measurable_integrable.1 i)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))]
  have hbound := (absorption_and_expected_changes θ hθ0 hθ1 i).2
  have hfinite : expectedChanges (ENNReal.ofReal θ) i < ⊤ := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  unfold expectedChanges at hfinite
  apply lt_of_le_of_lt _ hfinite
  apply lintegral_mono
  intro ω
  simpa using up_le_changes ω i
