-- Prove2me | solution 1 for AvramDividend.Classical.chat03_finite_horizon_scale_square_compensator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:16:39.224062+00:00
-- url     : https://prove2.me/submissions/cdd72358-c940-4b02-a346-6e0a14480da8

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_square_exponential_bound
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Finite-horizon q-scale square domination by the compensated exponential
at parameter 2θ. This is valid at every deterministic or random time t≤N.
The grid optional-sampling theorem supplies its future expected value.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x z : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (ht : t ≤ N) :
    (Real.exp (-(q * (t : ℝ))) * W (x + z)) ^ 2 ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0) *
        Real.exp (2 * θ * z - (t : ℝ) * X.ψ (2 * θ)) := by
  let B : ℝ := (X.ψ θ - q)⁻¹
  let c : ℝ := X.ψ (2 * θ)
  have hSquare :=
    chat03_discounted_scale_square_exponential_bound
      X q hq W hW θ (x + z) hθ hψ t
  have htR : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast ht
  have hc : c ≤ max c 0 := le_max_left _ _
  have hcnonneg : 0 ≤ max c 0 := le_max_right _ _
  have hclock : (t : ℝ) * c ≤ (N : ℝ) * max c 0 := calc
    (t : ℝ) * c ≤ (t : ℝ) * max c 0 :=
      mul_le_mul_of_nonneg_left hc t.property
    _ ≤ (N : ℝ) * max c 0 :=
      mul_le_mul_of_nonneg_right htR hcnonneg
  have hexp :
      Real.exp (2 * θ * ((x + z) + 1)) ≤
        Real.exp (2 * θ * (x + 1) + (N : ℝ) * max c 0) *
          Real.exp (2 * θ * z - (t : ℝ) * c) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hclock]
  have hsquare_exp :
      (Real.exp (θ * ((x + z) + 1)) * B)^2 =
        B^2 * Real.exp (2 * θ * ((x + z) + 1)) := by
    calc
      (Real.exp (θ * ((x + z) + 1)) * B)^2 =
          (Real.exp (θ * ((x + z) + 1)))^2 * B^2 := mul_pow _ _ _
      _ = B^2 * Real.exp
          (θ * ((x + z) + 1) + θ * ((x + z) + 1)) := by
        rw [pow_two, ← Real.exp_add]
        ring
      _ = B^2 * Real.exp (2 * θ * ((x + z) + 1)) := by
        congr 1
        ring
  change (Real.exp (-(q * (t : ℝ))) * W (x + z)) ^ 2 ≤
    B^2 * Real.exp (2 * θ * (x + 1) + (N : ℝ) * max c 0) *
    Real.exp (2 * θ * z - (t : ℝ) * c)
  calc
    (Real.exp (-(q * (t : ℝ))) * W (x + z)) ^ 2 ≤
        (Real.exp (θ * ((x + z) + 1)) * B)^2 := hSquare
    _ = B^2 * Real.exp (2 * θ * ((x + z) + 1)) := hsquare_exp
    _ ≤ B^2 * (Real.exp
        (2 * θ * (x + 1) + (N : ℝ) * max c 0) *
        Real.exp (2 * θ * z - (t : ℝ) * c)) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg B)
    _ = _ := by ring