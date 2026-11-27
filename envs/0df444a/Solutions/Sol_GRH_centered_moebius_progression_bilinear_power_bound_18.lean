-- Prove2me | solution 18 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T05:32:08.10961+00:00
-- url     : https://prove2.me/submissions/87ec472f-4367-4f19-b9f2-780cf185ffa8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency
import Theorems.Thm_GRH_fixed_rational_moebius_frequencies_escape_exceptional_square_cutoffs

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  obtain ⟨b,rfl⟩ := ha
  exact GRH.failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency.1
    GRH.fixed_rational_moebius_frequencies_escape_exceptional_square_cutoffs q (b : ZMod q) σ hhalf hone
