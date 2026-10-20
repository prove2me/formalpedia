-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_discounted_jump_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:29:32.995772+00:00
-- url     : https://prove2.me/submissions/8bf89464-5ad9-4cce-8f21-663fdc1d5d01

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_positive_magnitude_compensator_integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
The BV Esscher discounted compensator is integrable under nonnegative
arguments; the signed jump compensator is reduced to existing Proved facts.
-/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (φ s : ℝ) (hφ : 0 ≤ φ) (hs : 0 ≤ s) :
    Integrable (fun z : ℝ≥0 =>
      Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ)))))
      (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  have hplus : 0 ≤ φ + s := add_nonneg hφ hs
  have hnegative (u : ℝ) (hu : 0 ≤ u) :
      IntegrableOn (fun y : ℝ => 1 - Real.exp (u * y)) (Iio 0) X.ν := by
    have hneg := (bv_exponential_jump_integrable_nonneg X hbv u hu).neg
    have heq : EqOn (-(fun y : ℝ => Real.exp (u * y) - 1))
        (fun y : ℝ => 1 - Real.exp (u * y)) (Iio 0) := by
      intro y hy
      change -(Real.exp (u * y) - 1) = 1 - Real.exp (u * y)
      ring
    exact (integrableOn_congr_fun heq measurableSet_Iio).mp hneg
  have hJφ : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ)))) μ :=
    positive_magnitude_compensator_integrable X.ν φ (hnegative φ hφ)
  have hJplus : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-((φ + s) * (z : ℝ)))) μ :=
    positive_magnitude_compensator_integrable X.ν (φ + s)
      (hnegative (φ + s) hplus)
  have hsub := hJplus.sub hJφ
  change Integrable (fun z : ℝ≥0 =>
    (1 - Real.exp (-((φ + s) * (z : ℝ)))) -
      (1 - Real.exp (-(φ * (z : ℝ))))) μ at hsub
  have heq : (fun z : ℝ≥0 =>
    (1 - Real.exp (-((φ + s) * (z : ℝ)))) -
      (1 - Real.exp (-(φ * (z : ℝ))))) =
    (fun z : ℝ≥0 => Real.exp (-(φ * (z : ℝ))) *
      (1 - Real.exp (-(s * (z : ℝ))))) := by
    funext z
    have hmul : Real.exp (-((φ + s) * (z : ℝ))) =
        Real.exp (-(φ * (z : ℝ))) * Real.exp (-(s * (z : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hmul]
    ring
  rw [heq] at hsub
  exact hsub
