-- Prove2me | solution 1 for FamousTheorems.liouville_theorem_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:29:23.789693+00:00
-- url     : https://prove2.me/submissions/c75b572f-6272-4f11-a093-910353b77fcf

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (hf : InnerProductSpace.HarmonicOnNhd f Set.univ) (hb : Bornology.IsBounded (Set.range f)) :
    ∀ z w : ℂ, f z = f w :=
  InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant f hf hb
