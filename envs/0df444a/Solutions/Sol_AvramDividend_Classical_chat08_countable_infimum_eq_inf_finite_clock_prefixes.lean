-- Prove2me | solution 1 for AvramDividend.Classical.chat08_countable_infimum_eq_inf_finite_clock_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:59:21.053588+00:00
-- url     : https://prove2.me/submissions/66e5d27b-d661-42b7-987c-b504857f5502

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! Finite-prefix infima converge order-theoretically to the entire countable infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) :
    (⨅ n : ℕ,
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) ω) =
      (⨅ k : ℕ, τ k ω) := by
  let σ : ℕ → Ω → WithTop ℝ≥0 :=
    Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω))
  change (⨅ n, σ n ω) = (⨅ k, τ k ω)
  apply le_antisymm
  · apply le_iInf
    intro k
    calc
      (⨅ n, σ n ω) ≤ σ (k + 1) ω := iInf_le _ (k + 1)
      _ ≤ τ k ω := by
        change min (τ k ω) (σ k ω) ≤ τ k ω
        exact min_le_left _ _
  · apply le_iInf
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
        change (⨅ k, τ k ω) ≤ min (τ n ω) (σ n ω)
        exact le_min (iInf_le _ n) ih
