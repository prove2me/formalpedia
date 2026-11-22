-- Prove2me | solution 2 for GRH.reduced_liouville_harmonic_power_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:23.619244+00:00
-- url     : https://prove2.me/submissions/b0309f0c-2c38-4de1-9a6f-f6adb1bf3412
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_GRH_riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus

theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      |GRH.reducedLiouvilleHarmonic q U| ≤ K * ((U : ℝ) + 1) ^ (σ - 1) :=
  (GRH.riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus q).mp
    mathlib_riemannHypothesis σ hhalf hone
