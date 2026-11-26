-- Prove2me | solution 1 for GRH.moebius_real_dirichlet_prefix_bound_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:04:16.983988+00:00
-- url     : https://prove2.me/submissions/c388b9f7-dc6d-436e-8e48-83e349d9a74c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemannHypothesis_of_cofinal_negative_theta_gram
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound

open Finset
open scoped BigOperators

/- The real-prefix argument applies to every exponent above one half. -/
set_option linter.unusedVariables false in
theorem solution
    (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B := by
  have hRH := MasulloRH.riemannHypothesis_of_cofinal_negative_theta_gram
    MasulloRH.cofinal_theta_gram_negative_direction
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hhalf
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
  let f := fun j : ℕ => (ArithmeticFunction.moebius j : ℝ) * (j:ℝ)^(-σ)
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  refine ⟨max 0 B,le_max_left ..,?_⟩
  intro n
  change |∑ j ∈ range n, f j| ≤ _
  cases n with
  | zero => simp
  | succ n =>
    have he : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
    rw [he, sum_insert (by simp), show f 0 = 0 by simp [f], zero_add]
    exact (hB ⟨n,rfl⟩).trans (le_max_right ..)
