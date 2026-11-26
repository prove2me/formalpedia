-- Prove2me | solution 5 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:07:41.918906+00:00
-- url     : https://prove2.me/submissions/ec04c2ce-a95a-4701-954c-d10422ef18ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_square_block_control
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_of_cofinal_negative_theta_gram
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Theorems.Thm_GRH_moebius_residue_bias_of_primitive_zero_free_band
import Theorems.Thm_GRH_primitive_nonprincipal_LFunction_nonzero_below_record
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
    · apply Or.inr
      have hrecord := le_of_not_gt hhi
      let α : ℝ := (1/2 + σ)/2
      have hα : (1/2:ℝ) ≤ α := by dsimp [α]; linarith
      have hσ : α < σ := by dsimp [α]; linarith
      obtain ⟨C, hC, h⟩ := GRH.moebius_residue_bias_of_primitive_zero_free_band q α σ hα
        (hσ.le.trans hrecord) hσ
        (fun d _ _ ψ hp hψ s hs hr =>
          GRH.primitive_nonprincipal_LFunction_nonzero_below_record d ψ hp hψ s (hα.trans_lt hs) hr) a ha
      refine ⟨C, hC, ?_⟩
      intro u
      have e : ((u^2 : ℕ) : ℝ) = (u:ℝ)^2 := by norm_cast
      rw [← e]
      exact h (u^2)
