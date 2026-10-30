-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_tilt_split_49ac_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:18:30.891982+00:00
-- url     : https://prove2.me/submissions/88fc9fc7-5059-4d40-9488-b3c3a1b3c303

import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

-- Proof for published child:
-- AvramDividend.Classical.esscher_exp_tilt_split_49ac_bridge [3704a1c1]
-- Pure Mathlib; no Prove2Me premises. Binder names match the authoritative
-- statement exactly.
theorem solution (φ a b : ℝ) :
    Real.exp (φ * b) = Real.exp (φ * a) * Real.exp (φ * (b - a)) := by
  have h : φ * b = φ * a + φ * (b - a) := by ring
  rw [h, Real.exp_add]
