-- Prove2me | solution 2 for AvramDividend.Classical.causal_resolvent_C1_of_exponential_weighting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:25:12.419896+00:00
-- url     : https://prove2.me/submissions/c3ed5936-884b-43b5-bbe3-afcf0ae7b255

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_L1_primitive
import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Undo exponential weighting after the causal L1 resolvent smoothing. -/
theorem solution
    (f g k : ℝ → ℝ) (a θ : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x)
      (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hprim : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) =
        Real.exp (-(θ * x)) * g x)
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hres : ∀ x : ℝ, 0 < x →
      f x = g x - a *
        (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by
  have heNeg : ContDiff ℝ 1 (fun x : ℝ => Real.exp (-(θ * x))) := by
    fun_prop
  have hePos : ContDiff ℝ 1 (fun x : ℝ => Real.exp (θ * x)) := by
    fun_prop
  have hfcont : ContinuousOn
      (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ici (0 : ℝ)) :=
    heNeg.continuous.continuousOn.mul hf
  have hgdiff : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi (0 : ℝ)) :=
    heNeg.contDiffOn.mul hgC1
  have hresD : ∀ x : ℝ, 0 < x →
      Real.exp (-(θ * x)) * f x =
        Real.exp (-(θ * x)) * g x -
          a * (∫ s in Ioc (0 : ℝ) x,
            (Real.exp (-(θ * (x - s))) * f (x - s)) *
              (Real.exp (-(θ * s)) * g s) ∂volume) := by
    intro x hx
    rw [hres x hx]
    calc
      Real.exp (-(θ * x)) *
          (g x - a * (∫ s in Ioc (0 : ℝ) x,
            f (x - s) * g s ∂volume)) =
        Real.exp (-(θ * x)) * g x -
          a * (Real.exp (-(θ * x)) *
            (∫ s in Ioc (0 : ℝ) x,
              f (x - s) * g s ∂volume)) := by ring
      _ = _ := by
        rw [exponential_causal_convolution_factorisation f g θ x]
  have hFc1 : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi (0 : ℝ)) :=
    causal_resolvent_C1_of_L1_primitive
      (fun x : ℝ => Real.exp (-(θ * x)) * f x)
      (fun x : ℝ => Real.exp (-(θ * x)) * g x)
      k a hfcont hfL1 hkL1 hprim hgdiff hresD
  have hproduct : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (θ * x) *
        (Real.exp (-(θ * x)) * f x)) (Ioi (0 : ℝ)) :=
    hePos.contDiffOn.mul hFc1
  apply hproduct.congr
  intro x hx
  have hunit : Real.exp (θ * x) * Real.exp (-(θ * x)) = 1 := by
    rw [← Real.exp_add]
    simp
  symm
  calc
    Real.exp (θ * x) * (Real.exp (-(θ * x)) * f x) =
      (Real.exp (θ * x) * Real.exp (-(θ * x))) * f x := by ring
    _ = f x := by rw [hunit]; ring
