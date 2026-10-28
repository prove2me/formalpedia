-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_right_generator_add_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:20:16.809996+00:00
-- url     : https://prove2.me/submissions/23608279-8484-4e92-9858-9c85bb595af4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Additive closure of a Levy transition right-generator identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (x : ℝ)
    (hfInt : ∀ h : ℝ, Integrable
      (fun ω => f (x + X.X (Real.toNNReal h) ω)) P)
    (hgInt : ∀ h : ℝ, Integrable
      (fun ω => g (x + X.X (Real.toNNReal h) ω)) P)
    (hfSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator f x)))
    (hgSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, g (x + X.X (Real.toNNReal h) ω) ∂P) - g x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator g x)))
    (hGenerator : X.generator (fun z => f z + g z) x =
      X.generator f x + X.generator g x) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) +
                 g (x + X.X (Real.toNNReal h) ω) ∂P) -
          (f x + g x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z => f z + g z) x)) := by
  have hsum := hfSlope.add hgSlope
  have hlinear (h : ℝ) :
      (∫ ω, f (x + X.X (Real.toNNReal h) ω) +
              g (x + X.X (Real.toNNReal h) ω) ∂P) =
        (∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) +
        (∫ ω, g (x + X.X (Real.toNNReal h) ω) ∂P) :=
    integral_add (hfInt h) (hgInt h)
  have hevent :
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) +
                 g (x + X.X (Real.toNNReal h) ω) ∂P) -
          (f x + g x))) =ᶠ[
            nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x) +
        h⁻¹ * ((∫ ω, g (x + X.X (Real.toNNReal h) ω) ∂P) - g x)) := by
    apply Filter.Eventually.of_forall
    intro h
    dsimp only
    rw [hlinear h]
    ring
  rw [hGenerator]
  exact hsum.congr' hevent.symm
