-- Prove2me | solution 1 for GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:56:41.394529+00:00
-- url     : https://prove2.me/submissions/74df7ace-2221-4c14-947b-b771066ebc93

import Theorems.Thm_GRH_moebius_square_residual_iff_reduced_residue_bias
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound


/- The prefix indexing step follows the accepted harmonic proof
https://prove2.me/submissions/fb5b50f4-8dbf-495b-999d-76118ada7f21 . -/
open Finset
open scoped BigOperators

theorem solution
    (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ) ↔
    (q.totient = 1 ∨ ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ) := by
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hhalf
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
  let f := fun j : ℕ => (ArithmeticFunction.moebius j : ℝ) * (j:ℝ)^(-σ)
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  have hp (n : ℕ) : |∑ j ∈ range n, f j| ≤ max 0 B := by
    cases n with
    | zero => simp
    | succ n =>
      have he : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
      rw [he, sum_insert (by simp), show f 0 = 0 by simp [f], zero_add]
      exact (hB ⟨n,rfl⟩).trans (le_max_right ..)
  exact (GRH.centered_moebius_bound_iff_square_mertens_residual q a σ hhalf.le).trans
    (GRH.moebius_square_residual_iff_reduced_residue_bias q a ha σ (max 0 B)
      hhalf hone (le_max_left ..) hp)
