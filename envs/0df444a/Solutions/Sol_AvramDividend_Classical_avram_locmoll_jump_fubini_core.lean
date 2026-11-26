-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_jump_fubini_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:43:55.624508+00:00
-- url     : https://prove2.me/submissions/9b4148f9-963e-4c01-9a01-40cfe61d9464

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false
theorem solution
    (ν : Measure ℝ) [SFinite ν] (ρ : ℝ → ℝ)
    (K : ℝ → ℝ → ℝ) (G : ℝ → ℝ)
    (hP : Integrable (fun p : ℝ × ℝ => ρ p.1 * K p.1 p.2) (volume.prod ν))
    (he : ∀ᵐ z ∂ν, G z = ∫ r, ρ r * K r z) :
    Integrable G ν ∧ Integrable (fun r => ρ r * (∫ z, K r z ∂ν)) ∧
      (∫ z, G z ∂ν) = ∫ r, ρ r * (∫ z, K r z ∂ν) := by 
  have h1 : Integrable (fun r => ∫ z, ρ r * K r z ∂ν) :=
    hP.integral_prod_left
  have h2 : Integrable (fun z => ∫ r, ρ r * K r z) ν :=
    hP.integral_prod_right
  have he' : (fun z => ∫ r, ρ r * K r z) =ᵐ[ν] G := by
    filter_upwards [he] with z hz
    exact hz.symm
  refine ⟨h2.congr he', ?_, ?_⟩
  · simpa only [integral_const_mul] using h1
  · calc
      _ = ∫ z, (∫ r, ρ r * K r z) ∂ν := integral_congr_ae he
      _ = ∫ r, (∫ z, ρ r * K r z ∂ν) :=
        (integral_integral_swap hP).symm
      _ = _ := by simp only [integral_const_mul]
