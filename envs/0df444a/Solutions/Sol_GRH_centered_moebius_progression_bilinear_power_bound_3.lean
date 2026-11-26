-- Prove2me | solution 3 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:10:11.611919+00:00
-- url     : https://prove2.me/submissions/8aa98143-80cc-45bb-9f61-cd6f415cc872
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_moebius_square_mertens_harmonic_residual_below_boundary
import Theorems.Thm_GRH_centered_moebius_square_block_control

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by 
  by_cases hrecord : (0.8749570698 : ℝ) < σ
  · exact (GRH.centered_moebius_square_block_control q a ha).2 σ hrecord hone
  · apply (GRH.centered_moebius_bound_iff_square_mertens_residual q a σ hhalf.le).2
    exact GRH.moebius_square_mertens_harmonic_residual_below_boundary
      q a ha σ hhalf (le_of_not_gt hrecord)
