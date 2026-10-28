-- Prove2me | solution 1 for AvramDividend.Classical.scale_resolvent_convolution_of_continuous_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:50:03.965971+00:00
-- url     : https://prove2.me/submissions/d1ef60ca-59c7-436e-9d5b-09970ebcadee

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scale_laplace_discount_resolvent_identity
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- The scale-function resolvent relation in real space, given regularity and
Laplace-integrability of the positive causal convolution. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ b : ℝ) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂)
    (hlarge : ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ)
    (hKcont : ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s))
      (Ioi (0 : ℝ)))
    (hKint : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)))
        (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by
  let K : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)
  let G : ℝ → ℝ := fun x => W₁ x + (q₂ - q₁) * K x
  have hW₁cont : ContinuousOn W₁ (Ioi (0 : ℝ)) :=
    hW₁.2.2.1.mono (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  have hW₂cont : ContinuousOn W₂ (Ioi (0 : ℝ)) :=
    hW₂.2.2.1.mono (by intro x hx; exact le_of_lt (Set.mem_Ioi.mp hx))
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) :=
    hW₁cont.add (continuousOn_const.mul hKcont)
  have hTransform : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W₂ x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * G x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * G x := by
    intro θ hθ
    obtain ⟨hθnn, hψ₁, hψ₂⟩ := hlarge θ hθ
    obtain ⟨hI₁, hLap₁⟩ := hW₁.2.2.2.2 θ hθnn hψ₁
    obtain ⟨hI₂, hLap₂⟩ := hW₂.2.2.2.2 θ hθnn hψ₂
    have hIK : IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) * K x) (Ioi 0) := hKint θ hθ
    have hFun : (fun x : ℝ => Real.exp (-(θ * x)) * G x) =
        (fun x : ℝ => Real.exp (-(θ * x)) * W₁ x +
          (q₂ - q₁) * (Real.exp (-(θ * x)) * K x)) := by
      funext x
      dsimp [G]
      ring
    have hIG : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * G x) (Ioi 0) := by
      rw [hFun]
      exact hI₁.add (hIK.const_mul (q₂ - q₁))
    have hIntG :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * G x) =
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) +
          (q₂ - q₁) * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * K x) := by
      rw [hFun, integral_add hI₁ (hIK.const_mul (q₂ - q₁)), integral_const_mul]
    have hConv := positive_causal_convolution_laplace_product W₁ W₂ θ hI₁ hI₂
    have hRes := scale_laplace_discount_resolvent_identity
      X q₁ q₂ θ hθnn hψ₁ hψ₂ W₁ W₂ hW₁ hW₂
    refine ⟨hI₂, hIG, ?_⟩
    calc
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x) =
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) +
            (q₂ - q₁) *
              ((∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) *
                (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₂ x)) := by
          nlinarith [hRes]
      _ = (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₁ x) +
            (q₂ - q₁) *
              (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * K x) := by rw [hConv]
      _ = ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * G x := hIntG.symm
  intro x hx
  simpa only [G, K] using
    continuousOn_Ioi_eq_of_laplace_eq_signed W₂ G b
      hW₂cont hGcont (by simpa only [neg_mul] using hTransform) x hx
