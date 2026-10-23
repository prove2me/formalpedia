-- Prove2me | solution 2 for AvramDividend.Classical.positive_weighted_causal_convolution_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:24:09.94526+00:00
-- url     : https://prove2.me/submissions/cff9130a-1122-403a-a101-df121ff5438c

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume))
      (Ioi (0 : ℝ)) volume := by
  let F : ℝ → ℝ := fun s => Real.exp (-(θ * s)) * f s
  let G : ℝ → ℝ := fun s => Real.exp (-(θ * s)) * g s
  have hi : Integrable
      (MeasureTheory.posConvolution F G
        (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
    MeasureTheory.integrable_posConvolution hf hg
      (ContinuousLinearMap.mul ℝ ℝ)
  have hpoint (x : ℝ) (hx : 0 < x) :
      MeasureTheory.posConvolution F G
        (ContinuousLinearMap.mul ℝ ℝ) volume x =
        Real.exp (-(θ * x)) *
          (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) := by
    unfold MeasureTheory.posConvolution
    simp only [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
      ContinuousLinearMap.mul_apply]
    change (∫ s in (0 : ℝ)..x, F s * G (x - s) ∂volume) = _
    rw [intervalIntegral.integral_of_le hx.le]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [F, G]
    have hexp : Real.exp (-(θ * s)) *
        Real.exp (-(θ * (x - s))) = Real.exp (-(θ * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (Real.exp (-(θ * s)) * f s) *
          (Real.exp (-(θ * (x - s))) * g (x - s)) =
        (Real.exp (-(θ * s)) *
          Real.exp (-(θ * (x - s)))) *
          (f s * g (x - s)) := by ring
      _ = _ := by rw [hexp]
  have heq :
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      MeasureTheory.posConvolution F G
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact (hpoint x hx).symm
  exact hi.integrableOn.congr heq.symm
