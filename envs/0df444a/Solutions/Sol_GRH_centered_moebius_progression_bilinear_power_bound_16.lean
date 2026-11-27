-- Prove2me | solution 16 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:48:07.084228+00:00
-- url     : https://prove2.me/submissions/4e778e03-fdd6-47af-a9ff-55215b395293
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_iff_cofinal_factorial_square_tests
import Theorems.Thm_GRH_cofinal_factorial_one_sided_moebius_squares

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ :=
  (GRH.centered_moebius_iff_cofinal_factorial_square_tests.1.mpr
    GRH.cofinal_factorial_one_sided_moebius_squares) q a ha σ hhalf hone
