-- Prove2me | solution 4 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:04:50.443807+00:00
-- url     : https://prove2.me/submissions/c53d4b34-7a83-41ac-8ec8-376dee943165
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_square_block_control
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_of_cofinal_negative_theta_gram
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Theorems.Thm_GRH_moebius_square_reduced_residue_bias_below_boundary
import Mathlib.Tactic.Linarith

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  by_cases hhi : (0.8749570698 : ℝ) < σ
  · exact (GRH.centered_moebius_square_block_control q a ha).2 σ hhi hone
  · have hRH := MasulloRH.riemannHypothesis_of_cofinal_negative_theta_gram
      MasulloRH.cofinal_theta_gram_negative_direction
    apply (GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
      hRH q a ha σ hhalf hone).2
    by_cases hcard : q.totient = 1
    · exact Or.inl hcard
    · have hpos := Nat.totient_pos.mpr (NeZero.pos q)
      exact Or.inr (GRH.moebius_square_reduced_residue_bias_below_boundary q a ha
        (by omega) σ hhalf (le_of_not_gt hhi))
