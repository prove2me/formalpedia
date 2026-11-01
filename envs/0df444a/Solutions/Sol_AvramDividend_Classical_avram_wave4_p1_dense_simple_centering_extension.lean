-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_dense_simple_centering_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:21:13.897008+00:00
-- url     : https://prove2.me/submissions/72cb10f5-00b6-4af3-9c5b-96141f8c9aa5

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- A continuous linear stochastic integral has zero expectation (or zero
past-weighted mean) for every L² integrand once that linear test vanishes on
a genuinely dense subspace of elementary predictable integrands. In source
applications, the test is expectation against a bounded past observable;
the elementary martingale property must still be proved from source law. -/
theorem solution
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (S : Submodule ℝ V)
    (hDense : DenseRange S.subtype)
    (I : V →L[ℝ] W)
    (L : W →L[ℝ] ℝ)
    (hElementary : ∀ x : S, L (I (x : V)) = 0) :
    ∀ v : V, L (I v) = 0 := by
  intro v
  refine hDense.induction ?_ ?_ v
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact hElementary y
  · exact isClosed_eq (L.continuous.comp I.continuous) continuous_const
