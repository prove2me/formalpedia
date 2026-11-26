-- Prove2me | solution 13 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:58:38.342901+00:00
-- url     : https://prove2.me/submissions/78a17f34-b742-4b4b-889d-412e49ed6447
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_iff_one_sided_residue_squares
import Theorems.Thm_GRH_one_sided_moebius_progression_upper_at_squares

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  exact GRH.centered_moebius_iff_one_sided_residue_squares.mpr
    GRH.one_sided_moebius_progression_upper_at_squares q a ha σ hhalf hone
