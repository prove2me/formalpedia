-- Prove2me | solution 1 for BookProof.WallEsaSemibounded.inner_toLp_self
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T07:00:19.227982+00:00
-- url     : https://prove2.me/submissions/37c827eb-9b7c-4785-9464-74ddd97469ca

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open MeasureTheory SchwartzMap

-- Direct proof from the registered statement using Mathlib.
theorem solution (g : 𝓢(ℝ, ℂ)) :
    (inner ℂ (g.toLp 2 (volume : Measure ℝ)) (g.toLp 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ∫ x : ℝ, inner ℂ (g x) (g x) :=
      SchwartzMap.inner_toL2_toL2_eq g g (volume : Measure ℝ)
    _ = ∫ x : ℝ, ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (g x)).trans
        (Complex.ofReal_pow ‖g x‖ 2).symm
    _ = _ := integral_complex_ofReal

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
