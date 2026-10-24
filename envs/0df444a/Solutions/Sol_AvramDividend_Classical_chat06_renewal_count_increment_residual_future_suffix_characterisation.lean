-- Prove2me | solution 1 for AvramDividend.Classical.chat06_renewal_count_increment_residual_future_suffix_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:28:17.269964+00:00
-- url     : https://prove2.me/submissions/c41c8803-93aa-4c62-aacb-fc687f034d5e

import Theorems.Thm_AvramDividend_Classical_chat06_renewal_count_increment_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_renewal_arrival_sum_past_residual_suffix_decomposition
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Express the post-clock arrival threshold using residual waiting time. -/
theorem solution
    {Ω : Type*}
    (τ : ℕ → Ω → ℝ)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (ω : Ω) (clock v : ℝ) (k : ℕ) :
    k < N ω (clock + v) - N ω clock ↔
      τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
        (∑ j ∈ Finset.range k, τ (N ω clock + 1 + j) ω) ≤ v := by
  rw [chat06_renewal_count_increment_arrival_threshold
    τ N hThreshold ω clock (clock + v) k]
  rw [chat06_renewal_arrival_sum_past_residual_suffix_decomposition
    (fun i => τ i ω) (N ω clock) k]
  constructor <;> intro h <;> linarith
