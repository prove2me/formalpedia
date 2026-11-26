-- Prove2me | solution 1 for GRH.moebius_square_mertens_harmonic_residual_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:56:42.936344+00:00
-- url     : https://prove2.me/submissions/c78b779e-3a45-4143-82db-917a22785d6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_moebius_square_residual_iff_reduced_residue_bias
import Theorems.Thm_GRH_moebius_square_reduced_residue_bias_below_boundary
import Theorems.Thm_GRH_moebius_real_dirichlet_prefix_bound_below_boundary
import Mathlib.Tactic.Linarith

open scoped BigOperators

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ := by
  obtain ⟨B,hB,hprefix⟩ := GRH.moebius_real_dirichlet_prefix_bound_below_boundary σ hhalf hrecord
  apply (GRH.moebius_square_residual_iff_reduced_residue_bias q a ha σ B hhalf
    (by linarith) hB hprefix).2
  by_cases hcard : q.totient = 1
  · exact Or.inl hcard
  · have hpos := Nat.totient_pos.mpr (NeZero.pos q)
    exact Or.inr (GRH.moebius_square_reduced_residue_bias_below_boundary q a ha
      (by omega) σ hhalf hrecord)
