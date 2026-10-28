-- Prove2me | solution 1 for AvramDividend.Classical.causal_resolvent_C1_of_exponential_weighting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:24:40.259999+00:00
-- url     : https://prove2.me/submissions/d8504695-2121-427d-87f9-75ca2989ef17

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_L1_primitive
import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
open AvramDividend.Classical MeasureTheory Set

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
  have hE : ContDiff ℝ 1 (fun x : ℝ => Real.exp (-(θ * x))) :=
    Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).neg)
  have hE' : ContDiff ℝ 1 (fun x : ℝ => Real.exp (θ * x)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have key := causal_resolvent_C1_of_L1_primitive
    (fun x => Real.exp (-(θ * x)) * f x) (fun x => Real.exp (-(θ * x)) * g x) k a
    ((hE.continuous.continuousOn).mul hf) hfL1 hkL1 hprim
    (hE.contDiffOn.mul hgC1) (by
      intro x hx
      have h := hres x hx
      have hfac := exponential_causal_convolution_factorisation f g θ x
      show Real.exp (-(θ * x)) * f x = Real.exp (-(θ * x)) * g x - a * _
      rw [h, mul_sub, ← hfac]; ring)
  refine (hE'.contDiffOn.mul key).congr (fun x _ => ?_)
  show f x = Real.exp (θ * x) * (Real.exp (-(θ * x)) * f x)
  rw [← mul_assoc, ← Real.exp_add]
  simp
