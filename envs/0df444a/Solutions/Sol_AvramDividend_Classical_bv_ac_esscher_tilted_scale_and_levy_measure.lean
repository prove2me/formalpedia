-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_tilted_scale_and_levy_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:20:48.412158+00:00
-- url     : https://prove2.me/submissions/0ce2bd44-3a94-43aa-8637-7c07a0b4483d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_bv_ac_levy_package
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ V : ℝ → ℝ,
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) ≪ volume ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
        ∂(X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ ∧
      (∀ x : ℝ, W x = Real.exp (φ * x) * V x) ∧
      (∀ θ : ℝ, 0 ≤ θ + φ → q < X.ψ (θ + φ) →
        IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume ∧
        (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
        (X.ψ (θ + φ) - q)⁻¹) := by
  obtain ⟨hneg, hacφ, hintφ⟩ :=
    esscher_bv_ac_levy_package X.ν φ hφ.le X.ν_Ici hac X.ν_integrable
  let V : ℝ → ℝ := fun y => Real.exp (-(φ * y)) * W y
  have htilt : ∀ x : ℝ, W x = Real.exp (φ * x) * V x := by
    intro x
    have he : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      W x = 1 * W x := (one_mul _).symm
      _ = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by
        rw [he]
      _ = Real.exp (φ * x) * V x := by
        dsimp [V]
        ring
  refine ⟨V, hneg, hacφ, hintφ, htilt, ?_⟩
  intro θ hθ hψ
  simpa only [V] using
    (esscher_tilted_scale_laplace_shift X q W hW φ θ hθ hψ)
