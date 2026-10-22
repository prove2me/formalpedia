-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_inclusive_drift_adjusted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:56:09.283711+00:00
-- url     : https://prove2.me/submissions/2c5cd71d-e881-423c-9d00-3e884a56c8d5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_pushforward_unit_atom
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_real_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_unit_atom_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_unit_atom_real_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The actual Lévy exponent has the inclusive Gaussian jump kernel
when its linear drift is corrected by the finite unit-jump intensity. -/
theorem solution (c σ θ : ℝ) (ν : Measure ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(ν.map (fun y : ℝ => -y))) < ⊤) :
    laplaceExponent c σ ν θ =
      (c - (ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ)) * θ +
        σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-θ * z) - 1 +
            θ * (if z ≤ 1 then z else 0)
              ∂(ν.map (fun y : ℝ => -y))) := by
  let μ : Measure ℝ := ν.map (fun y : ℝ => -y)
  let J : ℝ → ℝ := fun z =>
    Real.exp (-θ * z) - 1 + θ * (if z ≤ 1 then z else 0)
  let A : ℝ → ℝ := fun z =>
    θ * (if z = 1 then (1 : ℝ) else 0)
  have hJ : IntegrableOn J (Ioi (0 : ℝ)) μ := by
    simpa only [J] using
      gaussian_levy_jump_real_integrable μ θ hθ hlevy
  have hAeq : A = ({1} : Set ℝ).indicator (fun _ => θ) := by
    funext z
    by_cases hz : z = 1
    · subst z
      simp [A]
    · simp [A, Set.indicator, hz]
  have hA : IntegrableOn A (Ioi (0 : ℝ)) μ := by
    rw [hAeq]
    exact (gaussian_levy_unit_atom_integrable μ θ hlevy).integrableOn
  have hsplit :
      (∫ z in Ioi (0 : ℝ), J z - A z ∂μ) =
        (∫ z in Ioi (0 : ℝ), J z ∂μ) -
          (∫ z in Ioi (0 : ℝ), A z ∂μ) :=
    integral_sub hJ hA
  have hunit : (∫ z in Ioi (0 : ℝ), A z ∂μ) =
      θ * μ.real ({1} : Set ℝ) := by
    simpa only [A] using gaussian_unit_atom_real_integral μ θ
  calc
    laplaceExponent c σ ν θ = c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ), J z - A z ∂μ) := by
      simpa only [J, A, μ] using
        gaussian_laplaceExponent_pushforward_unit_atom c σ θ ν
    _ = c * θ + σ ^ 2 * θ ^ 2 / 2 +
        ((∫ z in Ioi (0 : ℝ), J z ∂μ) -
          (∫ z in Ioi (0 : ℝ), A z ∂μ)) := by rw [hsplit]
    _ = _ := by
      rw [hunit]
      ring
