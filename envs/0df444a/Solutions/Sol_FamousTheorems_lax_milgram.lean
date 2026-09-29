-- Prove2me | solution 1 for FamousTheorems.lax_milgram
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:24.671895+00:00
-- url     : https://prove2.me/submissions/2a69001c-c439-4b27-9c20-988142a5e592

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B) :
    Nonempty (V ≃L[ℝ] V) := ⟨coercive.continuousLinearEquivOfBilin⟩
