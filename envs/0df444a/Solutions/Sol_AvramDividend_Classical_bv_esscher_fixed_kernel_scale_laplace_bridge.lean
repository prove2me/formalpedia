-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_fixed_kernel_scale_laplace_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:15:51.205471+00:00
-- url     : https://prove2.me/submissions/f12e9816-3802-4c3a-a412-aa2685b97bb1

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_fixed_kernel_denominator_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (κ β : Measure ℝ) (hκsf : SFinite κ)
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκmass : κ Set.univ < ENNReal.ofReal X.drift)
    (hκLap : ∀ s : ℝ, 0 < s →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(s * z))) ∂κ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))
    (hβlocal : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hβLap : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal X.drift)⁻¹ *
          (1 - (ENNReal.ofReal X.drift)⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        (Real.exp (-(φ * x)) * W x)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        (Real.exp (-(φ * x)) * W x)) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * (β (Iic x)).toReal) := by 
  refine ⟨max 0 (1 - φ), fun θ hθ => ?_⟩
  obtain ⟨hψ, hden⟩ := bv_esscher_fixed_kernel_denominator_identity X hX q hq W hW hbv φ hφ hroot
    κ hκsf hκsupp hκmass hκLap θ hθ
  have hθ0 : 0 < θ := lt_of_le_of_lt (le_max_left _ _) hθ
  have hθφ : 0 ≤ θ + φ := by linarith
  have hfeq : (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-(φ * x)) * W x)) =
      fun x => Real.exp (-((θ + φ) * x)) * W x := by
    funext x; rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-(φ * x)) * W x))
      (Ioi 0) := by
    rw [hfeq]; exact (hW.2.2.2.2 (θ + φ) hθφ hψ).1
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-(φ * x)) * W x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hW.2.1 x (le_of_lt hx)))
  have htilt := scaleFunction_tilted_positive_lintegral X q W hW θ φ hθφ hψ
  simp only [neg_mul] at htilt
  have hLap : (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-θ * x) * (Real.exp (-(φ * x)) * W x))) =
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x)) := by
    rw [hβLap θ hθ0, ← hden]
    simpa only [neg_mul] using htilt
  obtain ⟨hβi, heq⟩ := positive_cumulative_laplace_real_integral_bridge β hβlocal θ _ hint hpos hLap
  exact ⟨hint, hβi, heq⟩
