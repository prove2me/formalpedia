-- Prove2me | solution 1 for CountingLLL.ContractedWalk.iid_ae_stopped_prefix_independent
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T08:04:56.004169+00:00
-- url     : https://prove2.me/submissions/a1a1b57d-f7c8-4222-9a19-9d01a6aa042a

import Definitions.Def_CountingLLL_ContractedWalk
import Theorems.Thm_CountingLLL_ContractedWalk_iid_ae_strong_markov

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → Option ℕ) (R : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = some n ↔ τ ω' = some n))
    (hR : ∀ n ω ω', (∀ k < n, ω k = ω' k) → τ ω = some n → R ω = R ω')
    (hfin : ∀ᵐ ω ∂tapeLaw p, τ ω ≠ none) :
    IndepFun R (fun ω k => ω (k+(τ ω).getD 0)) (tapeLaw p) :=
  (CountingLLL.ContractedWalk.iid_ae_strong_markov p hp τ R hτ hR hfin).1
