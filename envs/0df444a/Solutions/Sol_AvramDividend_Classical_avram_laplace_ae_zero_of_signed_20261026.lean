-- Prove2me | solution 1 for AvramDividend.Classical.avram_laplace_ae_zero_of_signed_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:12:11.555983+00:00
-- url     : https://prove2.me/submissions/b3fa99a7-f458-4deb-9de1-257c2bec5e6f

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_avram_laplace_ae_eq_of_nonnegative_20261026

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open AvramDividend.Classical

/-- Signed Laplace uniqueness from nonnegative Laplace uniqueness. -/
theorem solution
    (R : ℝ → ℝ) (b : ℝ)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * R x) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) = 0) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), R x = 0 := by
  let f : ℝ → ℝ := fun x => R x + |R x|
  let g : ℝ → ℝ := fun x => |R x|
  let μ0 : Measure ℝ := volume.restrict (Ioi 0)
  have hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
    intro x _
    dsimp [f]
    linarith [neg_le_abs (R x)]
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x := by
    intro x _
    exact abs_nonneg _
  have hlapParts (θ : ℝ) (hθ : b < θ) :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x := by
    obtain ⟨hRi, hRzero⟩ := hlap θ hθ
    have hRi' : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * R x) μ0 := by
      simpa only [μ0] using hRi.integrable
    have hgi : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * g x) μ0 := by
      simpa only [g, abs_mul, abs_of_pos (Real.exp_pos _)] using hRi'.abs
    have hfi : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * f x) μ0 := by
      have hfadd :
          (fun x : ℝ => Real.exp (-(θ * x)) * f x) =
          (fun x : ℝ => Real.exp (-(θ * x)) * R x) +
          (fun x : ℝ => Real.exp (-(θ * x)) * g x) := by
        funext x
        simp [f, g, mul_add, Pi.add_apply]
      rw [hfadd]
      exact hRi'.add hgi
    refine ⟨hfi, hgi, ?_⟩
    have hsum :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x := by
      simpa only [f, g, mul_add] using (integral_add hRi' hgi)
    rw [hsum, hRzero, zero_add]
  have hae : f =ᵐ[μ0] g :=
    avram_laplace_ae_eq_of_nonnegative_20261026
      f g b hfnonneg hgnonneg hlapParts
  have hRzero : ∀ᵐ x ∂μ0, R x = 0 := by
    filter_upwards [hae] with x h
    dsimp [f, g] at h
    linarith
  simpa only [μ0] using hRzero
