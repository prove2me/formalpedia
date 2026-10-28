-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_right_generator_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:20:13.66362+00:00
-- url     : https://prove2.me/submissions/0233182a-285d-4cbd-bfb4-3385eaa060ea

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Scalar closure for an identified Levy transition right-generator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (k x : ℝ)
    (hfSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator f x))) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, k * f (x + X.X (Real.toNNReal h) ω) ∂P) -
          k * f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z => k * f z) x)) := by
  have hlim := hfSlope.const_mul k
  have hlinear (h : ℝ) :
      (∫ ω, k * f (x + X.X (Real.toNNReal h) ω) ∂P) =
        k * (∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) := by
    rw [integral_const_mul]
  have hevent :
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, k * f (x + X.X (Real.toNNReal h) ω) ∂P) -
          k * f x)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun h : ℝ => k * (h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x))) := by
    apply Filter.Eventually.of_forall
    intro h
    dsimp only
    rw [hlinear h]
    ring
  rw [levy_generator_const_mul]
  exact hlim.congr' hevent.symm
