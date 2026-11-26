-- Prove2me | solution 7 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:43:55.683148+00:00
-- url     : https://prove2.me/submissions/2dc10ad5-a73c-4b44-a169-352269e77167
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_square_block_control
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_of_cofinal_negative_theta_gram
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Theorems.Thm_GRH_moebius_residue_bias_of_primitive_zero_free_band
import Theorems.Thm_GRH_dirichlet_band_nonzero_iff_cofinal_finite_grids
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_GRH_dirichlet_grid_of_period_cover
import Theorems.Thm_GRH_first_two_dirichlet_grids_at_small_levels
import Theorems.Thm_GRH_primitive_dirichlet_grids_outside_period_covers

private theorem certified_grid
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) : ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  by_cases e : (h=0 ∧ (d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30)) ∨ (h=1 ∧ (d ∣ 4 ∨ d ∣ 6))
  · exact GRH.first_two_dirichlet_grids_at_small_levels d ψ hψ h e
  · let a := 1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
    by_cases hw : GRH.DirichletPeriod.Covers d a ((h:ℝ)+1)
    · have hpos : (0:ℝ) ≤ (0.8749570698:ℝ)-1/2 := by norm_num
      have hleft : (1/2:ℝ) ≤ a := le_add_of_nonneg_right (div_nonneg hpos (by positivity))
      have hright : a ≤ (0.8749570698:ℝ) := by
        have hdiv := div_le_self hpos (show 1 ≤ (h:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) h])
        dsimp [a]
        linarith
      exact GRH.dirichlet_grid_of_period_cover d ψ hψ a _ _ hleft hright (by norm_num) (by positivity) hw
    · exact GRH.primitive_dirichlet_grids_outside_period_covers d ψ hprim hψ h hw

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
          (GRH.dirichlet_band_nonzero_iff_cofinal_finite_grids d ψ hψ (0.8749570698:ℝ)
            (by norm_num) (by norm_num)).2
            (certified_grid d ψ hp hψ) s (hα.trans_lt hs) hr) a ha
      refine ⟨C, hC, ?_⟩
      intro u
      have e : ((u^2 : ℕ) : ℝ) = (u:ℝ)^2 := by norm_cast
      rw [← e]
      exact h (u^2)
